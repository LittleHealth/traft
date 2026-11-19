#!/usr/bin/env python3
"""Test the acceptance parser against false-positive failure modes, on dq-179."""
import json
import os
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'models'))
from run_proofs import (classify, module_wall_limit, proof_groups, LONG_COMPOSITION_MODULES,
                        stat_group_rss, memory_resources, runtime_profile, runtime_environment,
                        directory_bytes)
from run_proof_group import split_module_results
import run_proofs as proof_runner
from tla_audit import holes, dependencies, proof_dependencies, union_parentheses_violations
from acceptance import REQUIRED_STAGES, stage_coverage, proof_status_coverage
from toolchain_audit import proof_runtime_matches
from audit_client_source_changes import admission_delta, OLD_BOUNDARY, NEW_BOUNDARY


def block(**fields):
    return '@!!BEGIN\n' + ''.join('@!!' + k + ':' + str(v) + '\n' for k, v in fields.items()) + '@!!END\n'


def main():
    cases = []
    count = block(type='obligationsnumber', count=1)
    good = count + block(type='obligation', id=1, status='proved', already='false') + '[INFO]: All 1 obligation proved.\n'
    def check(name, condition):
        cases.append({'case': name, 'passed': bool(condition)})
    check('client capacity audit requires the exact added local alternative',
          admission_delta('Before\n' + OLD_BOUNDARY + 'After\n',
                          'Before\n' + NEW_BOUNDARY + 'After\n')
          and not admission_delta(OLD_BOUNDARY, OLD_BOUNDARY))
    check('client capacity audit rejects global safety guards and unrelated changes',
          not admission_delta(OLD_BOUNDARY, NEW_BOUNDARY + 'Next == Safety /\\ Action\n')
          and not admission_delta(OLD_BOUNDARY, NEW_BOUNDARY.replace('Count(L, Cur(L))', 'GlobalCount'))
          and not admission_delta(OLD_BOUNDARY + OLD_BOUNDARY, NEW_BOUNDARY + NEW_BOUNDARY))
    check('success requires status and coverage', classify(good, 0)['outcome'] == 'proved')
    check('exit zero with false obligation rejected', classify(count + block(type='obligation', id=1, status='failed', reason='false'), 0)['outcome'] == 'unproved')
    check('missing obligation rejected', classify(good.replace('count:1', 'count:2'), 0)['outcome'] == 'unproved')
    check('missing summary rejected', classify(good.split('[INFO]')[0], 0)['outcome'] == 'unproved')
    check('timeout is not success', classify(good, 0, 'timeout')['outcome'] == 'timeout')
    check('dependency error rejected', classify('[ERROR]: dependency failed\n' + good, 0)['outcome'] == 'unproved')
    check('zero obligations rejected', classify(block(type='obligationsnumber', count=0) + '[INFO]: All 0 obligation proved.', 0)['outcome'] == 'unproved')
    check('resident resource stop cannot become proof success',
          classify(good, 0, 'resident_limit')['outcome'] == 'resident_limit')
    check('monitor failure cannot become proof success',
          classify(good, 0, 'monitor_error')['outcome'] == 'monitor_error')
    with tempfile.TemporaryDirectory(prefix='traft-disk-monitor-') as directory:
        root = Path(directory)
        (root / 'stable').write_bytes(b'12345')
        (root / 'nested').mkdir()
        (root / 'nested' / 'stable').write_bytes(b'678')
        disappearing = root / 'temporary'
        disappearing.write_bytes(b'123456789')
        real_stat = Path.stat
        def remove_before_stat(path, *args, **kwargs):
            if path == disappearing:
                disappearing.unlink()
            return real_stat(path, *args, **kwargs)
        with patch.object(Path, 'stat', remove_before_stat):
            check('disk sampling tolerates a backend deleting an enumerated temporary file',
                  directory_bytes(root) == 8)
        def deny_stable_stat(path, *args, **kwargs):
            if path == root / 'stable':
                raise PermissionError('injected unreadable file metadata')
            return real_stat(path, *args, **kwargs)
        try:
            with patch.object(Path, 'stat', deny_stable_stat):
                directory_bytes(root)
        except PermissionError:
            unreadable_rejected = True
        else:
            unreadable_rejected = False
        check('disk sampling propagates permission errors instead of undercounting', unreadable_rejected)
    stat_fields = ['S', '4', '12'] + ['0'] * 18 + ['25'] + ['0'] * 12
    check('process RSS accounting handles parentheses inside process names',
          stat_group_rss('99 (poly (worker)) ' + ' '.join(stat_fields), 4096) == (12, 102400))
    modern_memory = memory_resources('polyml-reserved', 12345)
    check('reserved address profile retains resident and PolyML heap bounds',
          modern_memory['per_process_address_space_gib'] == 2
          and modern_memory['polyml_virtual_address_space_gib'] == 32
          and modern_memory['polyml_heap_mib'] == 512
          and modern_memory['polyml_gc_threads'] == 1
          and modern_memory['group_resident_cap_gib'] == 2
          and modern_memory['peak_group_resident_bytes_sampled'] == 12345)
    try:
        runtime_profile(type('Args', (), {'runtime_profile': 'unbounded'})())
    except ValueError:
        bad_profile_rejected = True
    else:
        bad_profile_rejected = False
    check('unknown runtime profile rejected', bad_profile_rejected)
    previous = os.environ.get('OCAMLRUNPARAM')
    os.environ['OCAMLRUNPARAM'] = 'o=20'
    check('diagnostic OCaml parameters cannot leak into formal runs',
          'OCAMLRUNPARAM' not in runtime_environment('polyml-reserved'))
    if previous is None:
        os.environ.pop('OCAMLRUNPARAM')
    else:
        os.environ['OCAMLRUNPARAM'] = previous
    checked = classify(good, 0)
    check('acceptance checks successful individual statuses', proof_status_coverage(checked, 1))
    check('acceptance rejects unknown expected count', not proof_status_coverage(checked, None))
    check('acceptance rejects forged success label on failed status',
          not proof_status_coverage(dict(checked, obligations={'1': {'status': 'failed'}}), 1))
    check('acceptance rejects absent final statuses',
          not proof_status_coverage(dict(checked, obligations={}), 1))
    check('acceptance rejects a cached obligation despite a successful status',
          not proof_status_coverage(dict(checked, obligations={
              '1': {'status': 'proved', 'already': 'true'}}), 1))
    check('acceptance rejects an obligation without the cache-use marker',
          not proof_status_coverage(dict(checked, obligations={
              '1': {'status': 'proved'}}), 1))
    tool_audit = {'accepted': True, 'runtime_profile': 'polyml-reserved', 'executable_sha256': 'checked-shim'}
    runtime_result = {'tlapm_sha256': 'checked-shim', 'proof_cache_reused': False,
                      'resources': dict(modern_memory, threads=1, cpu_affinity_max=2)}
    check('acceptance matches the tool and bounded runtime', proof_runtime_matches(runtime_result, tool_audit))
    check('acceptance rejects a different executable',
          not proof_runtime_matches(dict(runtime_result, tlapm_sha256='other-shim'), tool_audit))
    check('acceptance rejects fingerprint reuse',
          not proof_runtime_matches(dict(runtime_result, proof_cache_reused=True), tool_audit))
    check('acceptance rejects missing resident evidence',
          not proof_runtime_matches(dict(runtime_result, resources=dict(runtime_result['resources'],
              peak_group_resident_bytes_sampled=None)), tool_audit))
    check('acceptance rejects excess resident memory',
          not proof_runtime_matches(dict(runtime_result, resources=dict(runtime_result['resources'],
              peak_group_resident_bytes_sampled=2 * 1024**3 + 1)), tool_audit))
    reserved_memory = memory_resources('tlapm-reserved', 12345)
    reserved_audit = dict(tool_audit, runtime_profile='tlapm-reserved')
    reserved_result = dict(runtime_result, resources=dict(reserved_memory, threads=1, cpu_affinity_max=2))
    check('OCaml reservation preserves resident and PolyML heap caps',
          reserved_memory['per_process_address_space_gib'] == 4
          and reserved_memory['group_resident_cap_gib'] == 2
          and reserved_memory['polyml_heap_mib'] == 512
          and proof_runtime_matches(reserved_result, reserved_audit))
    check('virtual reservation does not permit higher resident memory',
          not proof_runtime_matches(dict(reserved_result, resources=dict(reserved_result['resources'],
              peak_group_resident_bytes_sampled=2 * 1024**3 + 1)), reserved_audit))
    check('runtime profiles cannot be interchanged',
          not proof_runtime_matches(reserved_result, tool_audit)
          and not proof_runtime_matches(runtime_result, reserved_audit))
    check('diagnostic runs never count as formal runtime evidence',
          not proof_runtime_matches(dict(reserved_result, resources=dict(reserved_result['resources'],
              diagnostic_only=True)), reserved_audit))
    bounded4_memory = memory_resources('tlapm-4g-resident', 3 * 1024**3)
    bounded4_audit = dict(tool_audit, runtime_profile='tlapm-4g-resident')
    bounded4_result = dict(runtime_result, resources=dict(bounded4_memory, threads=1, cpu_affinity_max=2))
    check('declared 4 GiB proof profile keeps virtual and backend heap bounds',
          bounded4_memory['per_process_address_space_gib'] == 8
          and bounded4_memory['group_resident_cap_gib'] == 4
          and bounded4_memory['polyml_heap_mib'] == 512
          and proof_runtime_matches(bounded4_result, bounded4_audit))
    check('4 GiB profile rejects excess resident memory and missing evidence',
          not proof_runtime_matches(dict(bounded4_result, resources=dict(bounded4_result['resources'],
              peak_group_resident_bytes_sampled=4 * 1024**3 + 1)), bounded4_audit)
          and not proof_runtime_matches(dict(bounded4_result, resources=dict(bounded4_result['resources'],
              peak_group_resident_bytes_sampled=None)), bounded4_audit))
    check('4 GiB proof records cannot be presented as 2 GiB runs',
          not proof_runtime_matches(bounded4_result, reserved_audit)
          and not proof_runtime_matches(reserved_result, bounded4_audit))
    bounded8_memory = memory_resources('tlapm-8g-resident', 5 * 1024**3)
    bounded8_audit = dict(tool_audit, runtime_profile='tlapm-8g-resident')
    bounded8_result = dict(runtime_result, resources=dict(bounded8_memory, threads=1, cpu_affinity_max=2))
    check('declared 8 GiB proof profile retains the backend heap bound',
          bounded8_memory['per_process_address_space_gib'] == 16
          and bounded8_memory['group_resident_cap_gib'] == 8
          and bounded8_memory['polyml_heap_mib'] == 512
          and proof_runtime_matches(bounded8_result, bounded8_audit))
    check('8 GiB profile rejects excess resident memory and missing evidence',
          not proof_runtime_matches(dict(bounded8_result, resources=dict(bounded8_result['resources'],
              peak_group_resident_bytes_sampled=8 * 1024**3 + 1)), bounded8_audit)
          and not proof_runtime_matches(dict(bounded8_result, resources=dict(bounded8_result['resources'],
              peak_group_resident_bytes_sampled=None)), bounded8_audit))
    check('8 GiB records cannot be relabelled as a smaller runtime profile',
          not proof_runtime_matches(bounded8_result, bounded4_audit)
          and not proof_runtime_matches(bounded4_result, bounded8_audit)
          and not proof_runtime_matches(bounded8_result, reserved_audit))
    check('leaf wall bound remains 300 seconds', module_wall_limit('TRaftFoldSimulation') == 300)
    check('ordinary composition wall bound remains 900 seconds', module_wall_limit('TRaftFormalSublogProof') == 900)
    check('client invariant identity imports use the bounded composition allowance',
          all(module_wall_limit('TRaftPointInvariantAliases' + n) == 900
              for n in ('01', '02', '03', '04'))
          and module_wall_limit('TRaftPointLiftInvariant') == 900)
    check('full invariant has separate frontend allowance', module_wall_limit('TRaftInvariantStepProof') == 1800)
    selected = ['LeafA', 'TRaftInvariantStepProof', 'LeafB', 'TRaftProtocolSafety', 'LeafC']
    scheduled = proof_groups(selected, 2, compositions_last=True)
    flattened = [m for group in scheduled for m in group]
    check('group scheduling preserves every requested module exactly once',
          len(flattened) == len(selected) and set(flattened) == set(selected))
    check('full-graph grouping keeps the resource cap and separate root groups',
          all(1 <= len(group) <= 2 for group in scheduled)
          and scheduled == [['LeafA', 'LeafB'], ['LeafC'],
                            ['TRaftInvariantStepProof', 'TRaftProtocolSafety']])
    # Exercise the CLI path: it previously ignored compositions-last when
    # group size was 1, even though the grouping helper itself was correct.
    with tempfile.TemporaryDirectory(prefix='traft-schedule-probe-') as tmp:
        observed_order = []
        def record_run(_args, module):
            observed_order.append(module)
            return {'outcome': 'proved'}
        argv = ['run_proofs.py', '--tlapm', str(Path(tmp) / 'unused-tlapm'),
                '--source', tmp, '--output', tmp, '--group-size', '1',
                '--group-compositions-last'] + selected
        with patch.object(sys, 'argv', argv), patch.object(proof_runner, 'run', record_run):
            schedule_rc = proof_runner.main()
        check('standalone CLI schedules every leaf before full-graph roots',
              schedule_rc == 0 and observed_order ==
              ['LeafA', 'LeafB', 'LeafC', 'TRaftInvariantStepProof', 'TRaftProtocolSafety'])
    try:
        proof_groups(['Repeated', 'Repeated'], 2, compositions_last=True)
    except ValueError:
        repeated_rejected = True
    else:
        repeated_rejected = False
    check('group scheduling rejects duplicate proof targets', repeated_rejected)
    roots = sorted(LONG_COMPOSITION_MODULES)
    check('trace decomposition keeps full-graph import wall allowance',
          all(module_wall_limit(module) == 1800 for module in
              ('TRaftClientTraceInterface', 'TRaftClientTraceState', 'TRaftClientTraceEvidence')))
    root_groups = proof_groups(roots, 4, compositions_last=True)
    check('balanced full-graph groups preserve order and total wall allowance',
          [m for group in root_groups for m in group] == roots
          and max(map(len, root_groups)) <= 4
          and max(map(len, root_groups)) - min(map(len, root_groups)) <= 1
          and sum(sum(module_wall_limit(m) for m in group) for group in root_groups)
              == sum(map(module_wall_limit, roots)))
    check('actual hole detected', holes('THEOREM Bad == FALSE\nPROOF OMITTED') == ['OMITTED'])
    check('comment and string not holes', not holes('(* outer (* OMITTED *) ADMITTED *)\nX == "OMITTED" \\* ADMITTED\n'))
    check('local imports detected', dependencies('EXTENDS A, B\n\nINSTANCE C WITH x <- 1\n') == {'A', 'B', 'C'})
    check('ambiguous UNION rejected', union_parentheses_violations('X == UNION {{}} \\cup {{}}') == [1])
    check('explicit UNION accepted', not union_parentheses_violations('X == (UNION {{}}) \\cup {{}}'))
    check('nested ambiguous UNION rejected', union_parentheses_violations('X == (UNION {UNION {{}} : x \\in S})') == [1])
    check('commented UNION ignored', not union_parentheses_violations('(* UNION {{}} *) X == "UNION {{}}"'))
    complete_stages = [{'name': name, 'returncode': 0} for name in REQUIRED_STAGES]
    check('complete successful stage coverage accepted', stage_coverage(complete_stages)['accepted'])
    check('capacity counterexample replay is a required stage',
          not stage_coverage([s for s in complete_stages if s['name'] != 'client_capacity_delta'])['accepted'])
    check('admission theorem syntax is a required stage',
          not stage_coverage([s for s in complete_stages if s['name'] != 'syntax_TRaftClientAdmissionProof'])['accepted'])
    check('missing client negative controls rejected',
          not stage_coverage([s for s in complete_stages if s['name'] != 'client_tlc'])['accepted'])
    check('missing source audit rejected',
          not stage_coverage([s for s in complete_stages if s['name'] != 'client_source_delta'])['accepted'])
    check('missing proof-source semantic preflight rejected',
          not stage_coverage([s for s in complete_stages if s['name'] != 'syntax_TRaftInvariantStepProof'])['accepted'])
    check('duplicate stage cannot fill coverage',
          not stage_coverage(complete_stages[:-1] + [complete_stages[0]])['accepted'])
    check('failed stage rejected',
          not stage_coverage(complete_stages[:-1] + [{'name': REQUIRED_STAGES[-1], 'returncode': 2}])['accepted'])
    good_module = good.replace('[INFO]', 'File "./Good.tla", line 1, character 1 to line 4, character 10:\n[INFO]')
    bad_module = (count + block(type='obligation', id=1, status='failed', reason='false')
                  + 'File "./Bad.tla", line 1, character 1 to line 4, character 10:\n'
                  + '[ERROR]: 1/1 obligation failed.\n')
    grouped = split_module_results(bad_module + good_module, ['Bad', 'Good'], 0)
    check('group keeps earlier false obligation', grouped['Bad'][0]['outcome'] == 'unproved')
    check('group separately reports later success', grouped['Good'][0]['outcome'] == 'proved')
    check('group rejects absent requested module',
          split_module_results(good_module, ['Missing'], 0)['Missing'][0]['outcome'] == 'missing_module_summary')
    check('group rejects duplicate module summary',
          split_module_results(good_module + good_module, ['Good'], 0)['Good'][0]['outcome'] == 'duplicate_module_summary')
    check('group does not accept incomplete trailing module',
          split_module_results(good_module + count, ['Good', 'Pending'], -15, 'timeout')['Pending'][0]['outcome'] == 'timeout')
    partial = ('(* module "Pending": 1 total obligations *)\n' + count
               + block(type='obligation', id=1, status='to be proved')
               + 'tlapm ending abnormally\n')
    crashed, _ = split_module_results(good_module + partial, ['Good', 'Pending'], 3)['Pending']
    check('group preserves uncompleted coverage after a prover crash',
          crashed['outcome'] == 'missing_module_summary' and crashed['obligations_expected'] == 1
          and crashed['unproved']['1']['status'] == 'to be proved')
    with tempfile.TemporaryDirectory(prefix='traft-dependency-probe-') as tmp:
        directory = Path(tmp)
        (directory / 'Root.tla').write_text('EXTENDS Middle\n\nTHEOREM Top == TRUE\nBY Hidden\n')
        (directory / 'Middle.tla').write_text('EXTENDS Leaf\n\nX == 1\n')
        (directory / 'Leaf.tla').write_text('THEOREM Hidden == FALSE\nBY SMT\n')
        needed = proof_dependencies(directory, 'Root')
        check('theorem-free middle does not hide failed import', needed == ['Leaf', 'Root'])
        checked = {'Root': True}
        check('root success alone cannot cover dependency', not all(checked.get(m, False) for m in needed))
        (directory / 'LocalRoot.tla').write_text('LOCAL HiddenProof == INSTANCE Leaf\n\nTHEOREM Top == TRUE\nBY HiddenProof!Hidden\n')
        local_needed = proof_dependencies(directory, 'LocalRoot')
        check('local proof instance remains an audited dependency', local_needed == ['Leaf', 'LocalRoot'])
        check('local failed lemma cannot be hidden by interface success',
              not all({'LocalRoot': True}.get(m, False) for m in local_needed))
    print(json.dumps(cases, indent=2))
    return int(not all(c['passed'] for c in cases))


if __name__ == '__main__':
    raise SystemExit(main())
