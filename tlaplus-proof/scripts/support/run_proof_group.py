#!/usr/bin/env python3
"""Check a small group of modules serially in one TLAPM process, without fingerprints.

TLAPM 1.5 accepts several input files and normalizes their common imports once.
Each requested module still generates and checks its own proof obligations.
Its positive/negative and shared-import selftests are required in each frozen run.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import uuid

from run_proofs import (classify, child_limits, digest, kill_group, module_wall_limit,
                        runtime_profile, runtime_environment, group_resident_bytes,
                        memory_resources, RUNTIME_PROFILES, resident_cap_gib, directory_bytes)
from tla_audit import holes, local_closure, proof_dependencies, union_parentheses_violations


# A module summary is emitted after all its obligation results. Error messages
# for individual obligations are not module summaries. Do not split on those.
SUMMARY = re.compile(
    r'File "(?:[^"\n]*/)?(?P<module>[A-Za-z_][A-Za-z_0-9]*)\.tla",[^\n]*:\s*\n'
    r'\[(?:INFO|ERROR)\]: (?:All \d+ obligations? proved\.|\d+/\d+ obligations? failed\.)')
MODULE_START = re.compile(r'(?m)^\(\* module "(?P<module>\w+)": \d+ total obligations \*\)')


def split_module_results(output, modules, returncode, terminated=None):
    """Reject absent/duplicate module summaries and preserve earlier failures."""
    pieces = {}
    begin = 0
    for match in SUMMARY.finditer(output):
        end = match.end()
        name = match.group('module')
        pieces.setdefault(name, []).append(output[begin:end] + '\n')
        begin = end
    rows = {}
    for name in modules:
        chunks = pieces.get(name, [])
        if len(chunks) != 1:
            # A frontend/backend crash may leave useful partial statuses but
            # no terminal module summary. Keep that evidence, never accept it.
            starts = list(MODULE_START.finditer(output))
            own_starts = [m for m in starts if m.group('module') == name]
            partial = ''
            if not chunks and len(own_starts) == 1:
                first = own_starts[0].start()
                end = next((m.start() for m in starts if m.start() > first), len(output))
                partial = output[first:end]
            row = classify(partial, returncode, terminated)
            row.update({'outcome': 'duplicate_module_summary' if chunks else terminated or 'missing_module_summary',
                        'module_summary_count': len(chunks),
                        'partial_coverage_available': bool(partial)})
            rows[name] = (row, partial)
            continue
        # A group-level error is never turned into an accepted group. Earlier
        # completed modules retain their own status; dependencies remain subject
        # to separate, source-matched acceptance.
        row = classify(chunks[0], 0)
        row['group_returncode'] = returncode
        row['group_termination'] = terminated
        row['module_summary_count'] = 1
        rows[name] = (row, chunks[0])
    return rows


def run_group(args):
    modules = args.modules
    if not 1 <= len(modules) <= 4 or len(set(modules)) != len(modules):
        raise ValueError('Use one to four distinct modules in a serial group.')
    wall_limit = sum(module_wall_limit(m) for m in modules)
    if not 0 < args.timeout <= wall_limit:
        raise ValueError('Group wall budget exceeds the sum of the named module allowances.')
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    group_id = stamp + '-group-' + uuid.uuid4().hex[:8]
    group_dir = args.output.parent / 'proof-groups' / group_id
    inputs = group_dir / 'input'
    inputs.mkdir(parents=True, exist_ok=False)
    hashes = {}
    for directory in args.source:
        for path in directory.glob('*.tla'):
            target = inputs / path.name
            if target.exists() and digest(target) != digest(path):
                raise ValueError('Conflicting module: ' + path.name)
            shutil.copyfile(path, target)
            hashes[path.name] = digest(target)
    closures = {m: local_closure(inputs, m) for m in modules}
    for name in sorted(set().union(*map(set, closures.values()))):
        source = (inputs / (name + '.tla')).read_text()
        if holes(source) or union_parentheses_violations(source):
            raise ValueError('Proof hole or ambiguous UNION in ' + name)
    command = [str(args.tlapm), '--threads', '1', '--nofp', '--timing',
               '--toolbox', '0', '0'] + [m + '.tla' for m in modules]
    profile = runtime_profile(args)
    before = time.monotonic()
    peak_resident = 0
    terminated = None
    monitor_error = None
    with (group_dir / 'output.log').open('w') as log:
        process = subprocess.Popen(command, cwd=inputs, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True, preexec_fn=lambda: child_limits(profile),
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
                if directory_bytes(group_dir) > 256 * 1024**2:
                    terminated = 'disk_limit'
                    break
                time.sleep(0.2)
        except OSError as error:
            terminated = 'monitor_error'
            monitor_error = repr(error)
        finally:
            if process.poll() is None:
                kill_group(process)
    output = (group_dir / 'output.log').read_text(errors='replace')
    elapsed = round(time.monotonic() - before, 3)
    group_backend_limits = [float(n) for n in re.findall(r'time-limit:\s*([0-9.]+)', output)]
    group_backend_limits_ok = all(n <= 60 for n in group_backend_limits)
    records = split_module_results(output, modules, process.returncode, terminated)
    global_error = bool(re.search(r'\[ERROR\]|ending abnormally|EXCEPTION|FATAL ERROR', output))
    resources = {'threads': 1, 'cpu_affinity_max': 2, **memory_resources(profile, peak_resident),
                 'group_wall_seconds': args.timeout, 'group_disk_gib': 0.25}
    results = []
    for module in modules:
        row, segment = records[module]
        if monitor_error is not None:
            row['monitor_error'] = monitor_error
        backend_limits = [float(n) for n in re.findall(r'time-limit:\s*([0-9.]+)', segment)]
        row.update({'module': module, 'input_sha256': hashes, 'command': command,
                    'tlapm_sha256': digest(args.tlapm), 'host': os.uname().nodename,
                    'resources': resources, 'elapsed_seconds': elapsed,
                    'elapsed_seconds_scope': 'shared group; do not sum module elapsed times',
                    'proof_cache_reused': False, 'union_syntax_audited': True,
                    'local_dependency_closure': closures[module],
                    'proof_dependencies_requiring_separate_runs': proof_dependencies(inputs, module),
                    'max_backend_time_limit_seconds': max(backend_limits, default=0),
                    'backend_time_limits_within_60_seconds': group_backend_limits_ok,
                    'group_max_backend_time_limit_seconds': max(group_backend_limits, default=0),
                    'group_directory': str(group_dir), 'group_modules': modules})
        if not row['backend_time_limits_within_60_seconds']:
            row['outcome'] = 'backend_limit_violation'
        destination = args.output / (stamp + '-' + module + '-' + uuid.uuid4().hex[:8])
        destination.mkdir(parents=True, exist_ok=False)
        (destination / 'output.log').write_text(segment)
        (destination / 'result.json').write_text(json.dumps(row, indent=2) + '\n')
        results.append({'module': module, 'outcome': row['outcome'],
                        'obligations_expected': row['obligations_expected'],
                        'unproved': list(row['unproved']), 'result': str(destination / 'result.json')})
    summary = {'group_id': group_id, 'modules': results, 'command': command, 'resources': resources,
               'elapsed_seconds': elapsed, 'returncode': process.returncode, 'termination': terminated,
               'global_error': global_error, 'input_sha256': hashes,
               'all_modules_proved': not terminated and process.returncode == 0 and not global_error
                    and group_backend_limits_ok
                    and all(r['outcome'] == 'proved' for r in results)}
    (group_dir / 'group-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: summary[k] for k in ('group_id', 'modules', 'elapsed_seconds', 'all_modules_proved')}), flush=True)
    return summary


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--tlapm', type=Path, required=True)
    parser.add_argument('--source', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=300)
    parser.add_argument('--runtime-profile', choices=RUNTIME_PROFILES, default='standard')
    args = parser.parse_args()
    args.tlapm = args.tlapm.resolve()
    args.source = [p.resolve() for p in args.source]
    args.output = args.output.resolve()
    raise SystemExit(0 if run_group(args)['all_modules_proved'] else 2)
