#!/usr/bin/env python3
"""Resource-bounded TLAPS runner; fail closed on missing/unproved obligations."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import stat
import subprocess
import time
import uuid
from tla_audit import holes, local_closure, proof_dependencies, union_parentheses_violations

SUCCESS = {'proved', 'trivial'}
# These modules assemble separately checked lemmas. TLAPM 1.5 normalizes
# imported modules before reporting their own obligations. The extra wall
# allowance covers that administrative work; backend limits remain <= 60 s.
COMPOSITION_MODULES = {
    # continuation-41 spent almost all 300 s normalizing imported lemmas:
    # eight own obligations completed, the remaining 66 were unattempted.
    'TRaftFormalSublogProof',
    # continuation-42 reached only 93/130 own obligations within 300 s.
    'TRaftClientPartitionActions',
    # continuation-43 proved 80/105 own obligations; the rest were not
    # attempted before 300 s after the shared partition-lemma import work.
    'TRaftClientRequestSources',
    'TRaftPrefixEvidenceInduction', 'TRaftCanonicalShapeInduction',
    'TRaftRecoveryInduction', 'TRaftSafetyClosureInduction',
    'TRaftInvariantStepProof', 'TRaftSafetyObligations', 'TRaftProtocolSafety',
    'TRaftClientPartitionTemporal', 'TRaftClientApplicationTemporal',
    'TRaftApplicationPrefixTemporal', 'TRaftApplicationAgreement',
    'TRaftClientHistoryTemporal',
    'TRaftClientTraceInterface', 'TRaftClientTraceState', 'TRaftClientTraceEvidence',
    'TRaftClientWitnessInduction',
    'TRaftClientLinearizationContext', 'TRaftClientLinearizability',
    'TRaftBoundedObserverRefinement',
    'TRaftClientCoreMapping',
    'TRaftUnboundedSafetyProof',
    'TRaftClientUnboundedProof',
    # These compare the protocol and client history instances. Run 19 spent
    # about 160 s importing the shared proof graph before checking identities.
    # Allow the same composition wall budget; each backend remains <= 60 s.
    'TRaftPointInvariantAliases01', 'TRaftPointInvariantAliases02',
    'TRaftPointInvariantAliases03', 'TRaftPointInvariantAliases04',
    'TRaftPointLiftInvariant',
}

# continuation-43 exhausted 900 s importing the full invariant's dependency
# graph before reporting any own obligation. These roots include that graph;
# the longer module wall allowance does not change a backend's time limit.
LONG_COMPOSITION_MODULES = {
    'TRaftInvariantStepProof', 'TRaftSafetyObligations', 'TRaftProtocolSafety',
    'TRaftClientPartitionTemporal', 'TRaftClientApplicationTemporal',
    'TRaftApplicationPrefixTemporal', 'TRaftApplicationAgreement',
    'TRaftClientHistoryTemporal', 'TRaftClientLinearizationContext',
    'TRaftClientTraceInterface', 'TRaftClientTraceState', 'TRaftClientTraceEvidence',
    'TRaftClientWitnessInduction',
    'TRaftClientLinearizability', 'TRaftBoundedObserverRefinement',
    'TRaftClientCoreMapping', 'TRaftUnboundedSafetyProof', 'TRaftClientUnboundedProof',
}


def module_wall_limit(module):
    return 1800 if module in LONG_COMPOSITION_MODULES else 900 if module in COMPOSITION_MODULES else 300


def proof_groups(modules, size, compositions_last=False):
    """Keep full-graph roots together without changing coverage or group limits."""
    if size not in (1, 2, 3, 4) or len(modules) != len(set(modules)):
        raise ValueError('Use distinct modules and a group size between one and four.')
    batches = [list(modules)]
    if compositions_last:
        batches = [[m for m in modules if m not in LONG_COMPOSITION_MODULES],
                   [m for m in modules if m in LONG_COMPOSITION_MODULES]]
    groups = []
    for batch in batches:
        if not batch:
            continue
        if not compositions_last:
            groups.extend(batch[offset:offset + size] for offset in range(0, len(batch), size))
            continue
        # Balance the final groups: fourteen full-graph roots become 4/4/3/3,
        # avoiding a small tail group that repeats the same large import work.
        # The number of processes, module coverage, and sum of wall limits stay
        # unchanged; no group exceeds the requested size.
        count = (len(batch) + size - 1) // size
        width, extra = divmod(len(batch), count)
        offset = 0
        for index in range(count):
            length = width + (index < extra)
            groups.append(batch[offset:offset + length])
            offset += length
    return groups


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def classify(output, returncode, terminated=None):
    states = {}
    count = None
    for item in re.finditer(r'@!!BEGIN\n(.*?)@!!END', output, re.S):
        fields = dict(re.findall(r'^@!!([^:\n]+):(.*)$', item.group(1), re.M))
        if fields.get('type') == 'obligation':
            if (fields.get('id') == '1' and fields.get('status') == 'to be proved'
                    and states.get('1', {}).get('status') in SUCCESS | {'failed', 'omitted', 'missing'}):
                states = {}
                count = None
            states[fields['id']] = fields
        elif fields.get('type') == 'obligationsnumber':
            count = int(fields['count'])
            if count == 0:
                states = {}
    summaries = re.findall(r'\[INFO\]: All (\d+) obligations? proved\.', output)
    total = int(summaries[-1]) if summaries else None
    bad = {k: v for k, v in states.items() if v.get('status') not in SUCCESS}
    failed = bool(re.search(r'\[ERROR\]|ending abnormally|EXCEPTION|FATAL ERROR', output))
    valid = (not terminated and returncode == 0 and not failed and count is not None
             and count > 0 and total == count and len(states) == count and not bad)
    return {'outcome': 'proved' if valid else terminated or 'unproved',
            'obligations_expected': count, 'obligations_reported': len(states),
            'obligations_proved_summary': total, 'obligations': states,
            'unproved': bad, 'returncode': returncode}


RUNTIME_PROFILES = ('standard', 'polyml-reserved', 'tlapm-reserved',
                    'tlapm-4g-resident', 'tlapm-8g-resident')


def resident_cap_gib(profile):
    return {'tlapm-4g-resident': 4, 'tlapm-8g-resident': 8}.get(profile, 2)


def address_space_gib(profile):
    return {'tlapm-reserved': 4, 'tlapm-4g-resident': 8,
            'tlapm-8g-resident': 16}.get(profile, 2)


def runtime_profile(args):
    profile = getattr(args, 'runtime_profile', 'standard')
    if profile not in RUNTIME_PROFILES:
        raise ValueError('Unknown proof runtime profile: ' + str(profile))
    return profile


def runtime_environment(profile):
    environment = dict(os.environ)
    for name in ('TLAPM_CACHE', 'TLAPM_NORMALIZE', 'TLAPM_FLATTEN', 'OCAMLRUNPARAM', 'CAMLRUNPARAM'):
        environment.pop(name, None)
    environment['TRAFT_PROOF_RUNTIME_PROFILE'] = profile
    return environment


def child_limits(profile='standard'):
    if profile not in RUNTIME_PROFILES:
        raise ValueError('Unknown proof runtime profile')
    os.nice(10)
    if hasattr(os, 'sched_getaffinity'):
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    # Virtual reservation is distinct from resident memory. The new profile
    # lets OCaml complete allocations with an explicit 2, 4 or 8 GiB group RSS
    # stop. Poly/ML separately reserves 32 GiB with a 512 MiB heap.
    hard = 2 if profile == 'standard' else 32
    soft = address_space_gib(profile)
    resource.setrlimit(resource.RLIMIT_AS, (soft * 1024**3, hard * 1024**3))


def stat_group_rss(stat, page_size):
    fields = stat.rsplit(')', 1)[1].split()
    return int(fields[2]), max(0, int(fields[21])) * page_size


def group_resident_bytes(group, proc=Path('/proc')):
    total = 0
    page_size = os.sysconf('SC_PAGE_SIZE')
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            owner, rss = stat_group_rss((entry / 'stat').read_text(), page_size)
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        if owner == group:
            total += rss
    return total


def directory_bytes(root):
    """Count logical file bytes while provers create/remove temporary files."""
    def walk_error(error):
        if not isinstance(error, FileNotFoundError):
            raise error
    total = 0
    for directory, _, filenames in os.walk(root, onerror=walk_error):
        for name in filenames:
            try:
                info = (Path(directory) / name).stat()
            except FileNotFoundError:
                # The file was removed after enumeration and consumes no
                # space in this sample. Other filesystem errors fail closed.
                continue
            if stat.S_ISREG(info.st_mode):
                total += info.st_size
    return total


def memory_resources(profile, peak):
    result = {'runtime_profile': profile,
              'per_process_address_space_gib': address_space_gib(profile),
              'ocaml_runtime_parameters': 'defaults'}
    if profile != 'standard':
        result.update({'polyml_virtual_address_space_gib': 32, 'polyml_heap_mib': 512,
                       'polyml_gc_threads': 1, 'group_resident_cap_gib': resident_cap_gib(profile),
                       'resident_sampling_seconds': 0.2,
                       'peak_group_resident_bytes_sampled': peak,
                       'resident_accounting': 'Sum of process-group RSS; shared pages may be counted twice.'})
    return result


def kill_group(process):
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=3)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
    except ProcessLookupError:
        pass


def run(args, module):
    if not 0 < args.timeout <= module_wall_limit(module):
        raise ValueError('Invalid wall budget for module: ' + module)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    run_dir = args.output / (stamp + '-' + module + '-' + uuid.uuid4().hex[:8])
    inputs = run_dir / 'input'
    inputs.mkdir(parents=True)
    hashes = {}
    for directory in args.source:
        for path in directory.glob('*.tla'):
            target = inputs / path.name
            if target.exists() and digest(target) != digest(path):
                raise ValueError('Conflicting input module: ' + path.name)
            shutil.copyfile(path, target)
            hashes[path.name] = digest(target)
    command = [str(args.tlapm), '--threads', '1', '--nofp', '--timing', '--toolbox', '0', '0',
               module + '.tla']
    closure = local_closure(inputs, module)
    for name in closure:
        if holes((inputs / (name + '.tla')).read_text()):
            raise ValueError('Proof holes in dependency: ' + name)
        bad_union = union_parentheses_violations((inputs / (name + '.tla')).read_text())
        if bad_union and not args.syntax_diagnostic:
            raise ValueError('Parenthesize UNION operands in ' + name + ': ' + str(bad_union))
    profile = runtime_profile(args)
    before = time.monotonic()
    peak_resident = 0
    terminated = None
    monitor_error = None
    with (run_dir / 'output.log').open('w') as log:
        process = subprocess.Popen(command, cwd=inputs, stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True,
                                   preexec_fn=lambda: child_limits(profile),
                                   env=runtime_environment(profile))
        try:
            while process.poll() is None:
                if profile != 'standard':
                    peak_resident = max(peak_resident, group_resident_bytes(process.pid))
                    if peak_resident > resident_cap_gib(profile) * 1024**3:
                        terminated = 'resident_limit'
                        break
                if time.monotonic() - before > args.timeout:
                    terminated = 'timeout'
                    break
                if directory_bytes(run_dir) > 256 * 1024**2:
                    terminated = 'disk_limit'
                    break
                time.sleep(0.2)
        except OSError as error:
            terminated = 'monitor_error'
            monitor_error = repr(error)
        finally:
            if process.poll() is None:
                kill_group(process)
    output = (run_dir / 'output.log').read_text(errors='replace')
    result = classify(output, process.returncode, terminated)
    if monitor_error is not None:
        result['monitor_error'] = monitor_error
    backend_limits = [float(n) for n in re.findall(r'time-limit:\s*([0-9.]+)', output)]
    result['max_backend_time_limit_seconds'] = max(backend_limits, default=0)
    result['backend_time_limits_within_60_seconds'] = all(n <= 60 for n in backend_limits)
    if not result['backend_time_limits_within_60_seconds']:
        result['outcome'] = 'backend_limit_violation'
    result.update({'module': module, 'input_sha256': hashes, 'command': command,
                   'elapsed_seconds': round(time.monotonic() - before, 3),
                   'tlapm_sha256': digest(args.tlapm), 'host': os.uname().nodename,
                   'resources': {'threads': 1, 'cpu_affinity_max': 2,
                                 **memory_resources(profile, peak_resident),
                                 'wall_seconds': args.timeout, 'disk_gib': 0.25},
                   'proof_cache_reused': False})
    result['union_syntax_audited'] = not args.syntax_diagnostic
    result['local_dependency_closure'] = closure
    result['proof_dependencies_requiring_separate_runs'] = proof_dependencies(inputs, module)
    (run_dir / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'module': module, 'outcome': result['outcome'],
                      'obligations': result['obligations_expected'],
                      'failed': list(result['unproved']), 'result': str(run_dir / 'result.json')}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--tlapm', type=Path, required=True)
    parser.add_argument('--source', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, default=Path('proof-results'))
    parser.add_argument('--timeout', type=float, default=120)
    parser.add_argument('--runtime-profile', choices=RUNTIME_PROFILES, default='standard')
    parser.add_argument('--composition-timeout', type=float,
                        help='Optional wall limit (<= 900 s) only for named composition modules; backend limits are unchanged.')
    parser.add_argument('--long-composition-timeout', type=float,
                        help='Optional wall limit (<= 1800 s) only for named roots importing the full invariant; backend limits are unchanged.')
    parser.add_argument('--syntax-diagnostic', action='store_true',
                        help='Only for the isolated UnionPrecedenceProof tool probe.')
    parser.add_argument('--group-size', type=int, choices=(1, 2, 3, 4), default=1,
                        help='Check up to four modules serially in one process; default keeps standalone runs.')
    parser.add_argument('--group-compositions-last', action='store_true',
                        help='Keep named full-graph roots in separate final groups; all requested modules are still checked.')
    args = parser.parse_args()
    if args.syntax_diagnostic and args.modules != ['UnionPrecedenceProof']:
        parser.error('--syntax-diagnostic is restricted to UnionPrecedenceProof')
    if args.group_size > 1 and (args.syntax_diagnostic or
                              {'ProofToolNegative', 'ProofToolSMTNegative'} & set(args.modules)):
        parser.error('Use the separate group selftest for intentional negative or syntax probes.')
    args.tlapm = args.tlapm.resolve()
    args.output = args.output.resolve()
    args.source = [p.resolve() for p in args.source]
    if args.timeout <= 0 or any(args.timeout > module_wall_limit(m) for m in args.modules):
        parser.error('Timeout exceeds a selected module limit (leaf 300 s, composition 900 s, named full root 1800 s).')
    if args.composition_timeout is not None and not 0 < args.composition_timeout <= 900:
        parser.error('Use 0 < composition-timeout <= 900.')
    if args.long_composition_timeout is not None and not 0 < args.long_composition_timeout <= 1800:
        parser.error('Use 0 < long-composition-timeout <= 1800.')
    def selected_arguments(module):
        run_args = argparse.Namespace(**vars(args))
        if module in COMPOSITION_MODULES and args.composition_timeout is not None:
            run_args.timeout = args.composition_timeout
        if module in LONG_COMPOSITION_MODULES and args.long_composition_timeout is not None:
            run_args.timeout = args.long_composition_timeout
        return run_args
    failed = False
    if args.group_size > 1:
        from run_proof_group import run_group
        for selected in proof_groups(args.modules, args.group_size, args.group_compositions_last):
            run_args = argparse.Namespace(**vars(args))
            run_args.modules = selected
            run_args.timeout = sum(selected_arguments(module).timeout for module in selected)
            failed |= not run_group(run_args)['all_modules_proved']
        return int(failed)
    # Honor the same ordering with standalone processes. Modern runs use
    # group size 1 to keep imported contexts within the resident-memory cap.
    for selected in proof_groups(args.modules, 1, args.group_compositions_last):
        module = selected[0]
        run_args = selected_arguments(module)
        result = run(run_args, module)
        if module in ('ProofToolNegative', 'ProofToolSMTNegative'):
            accepted = (result['outcome'] == 'unproved'
                        and result['obligations_expected'] == 2
                        and any(x.get('status') == 'failed' and x.get('reason') == 'false'
                                for x in result['unproved'].values()))
        else:
            accepted = result['outcome'] == 'proved'
        failed |= not accepted
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
