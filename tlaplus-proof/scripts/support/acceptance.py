#!/usr/bin/env python3
"""Accept only complete, source-matched proof chains; report open targets."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent / 'models'))
from tla_audit import code_only, local_closure, holes, proof_dependencies, union_parentheses_violations
from toolchain_audit import proof_runtime_matches

PROOF_SYNTAX_ROOTS = (
    'TRaftInvariantStepProof', 'TRaftClientUnboundedProof', 'TRaftUnboundedSafetyProof',
    'TRaftClientCoreMapping', 'TRaftDiagnosticProof', 'TRaftElectionProof',
    'TRaftEstablishedSafety', 'TRaftUnboundedHistoryProof', 'TRaftClientAdmissionProof',
)

REQUIRED_STAGES = (
    'parser_selftest', 'core_source_delta', 'client_source_delta',
    'prover_selftest', 'prover_group_selftest', 'source_semantics_selftest',
    'syntax_TRaftUnbounded', 'syntax_TRaftClientUnbounded',
    'syntax_TRaftProofScenarios', 'syntax_TRaftClientScenarios',
    'syntax_TRaftApplicationScenarios', 'syntax_TRaftFoldClientScenarios',
    'proofs', 'protocol_tlc', 'candidate_invariant_tlc', 'client_tlc', 'client_capacity_delta',
    'fold_equivalence_tlc', 'induction_diagnostic',
) + tuple('syntax_' + module for module in PROOF_SYNTAX_ROOTS)


def stage_coverage(stages):
    names = [stage['name'] for stage in stages]
    missing = [name for name in REQUIRED_STAGES if name not in names]
    repeated = sorted({name for name in names if names.count(name) != 1})
    unexpected = sorted(set(names) - set(REQUIRED_STAGES))
    accepted = (not missing and not repeated and not unexpected
                and all(stage['returncode'] == 0 for stage in stages))
    return {'accepted': accepted, 'missing': missing, 'repeated': repeated,
            'unexpected': unexpected, 'required': list(REQUIRED_STAGES)}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proof_status_coverage(result, expected):
    """Recheck every final obligation status, independently of the runner label."""
    states = result.get('obligations', {})
    return (isinstance(expected, int) and not isinstance(expected, bool) and expected > 0
            and result.get('outcome') == 'proved'
            and result.get('obligations_expected') == expected
            and result.get('obligations_reported') == expected
            and result.get('obligations_proved_summary') == expected
            and len(states) == expected and not result.get('unproved')
            and all(s.get('status') in ('proved', 'trivial')
                    and s.get('already') == 'false' for s in states.values()))


def assess(base, output):
    obligations = json.loads((base / 'proof-obligations.json').read_text())
    frozen = json.loads((base / 'source-manifest.json').read_text())
    changed = [name for name, sha in frozen['files'].items()
               if not (base / name).is_file() or digest(base / name) != sha]
    audits = []
    for name in ('toolchain-before.json', 'toolchain-after.json'):
        path = output / name
        audits.append(json.loads(path.read_text()) if path.is_file() else {})
    before, after = audits
    frozen_tool = output / 'toolchain.json'
    toolchain_ok = (before.get('accepted') and after.get('accepted')
                    and after.get('same_record_as_start')
                    and frozen_tool.is_file()
                    and before.get('toolchain_record_sha256') == digest(frozen_tool)
                    and before.get('toolchain_record_sha256') == after.get('toolchain_record_sha256'))
    modules = {}
    for name, count in obligations['checked_modules'].items():
        candidates = sorted((output / 'proofs').glob('*-' + name + '-*/result.json'))
        if not candidates:
            modules[name] = {'accepted': False, 'reason': 'no run in this frozen session'}
            continue
        path = candidates[-1]
        result = json.loads(path.read_text())
        closure = local_closure(base / 'models', name)
        matched = all(result['input_sha256'].get(m + '.tla') ==
                      frozen['files'].get('models/' + m + '.tla') for m in closure)
        hole_free = all(not holes((base / 'models' / (m + '.tla')).read_text()) for m in closure)
        syntax_audited = (result.get('union_syntax_audited', False)
                          and all(not union_parentheses_violations((base / 'models' / (m + '.tla')).read_text())
                                  for m in closure))
        statuses_complete = proof_status_coverage(result, count)
        runtime_matched = bool(toolchain_ok and proof_runtime_matches(result, before))
        accepted = (statuses_complete and matched and hole_free and syntax_audited
                    and runtime_matched
                    and result.get('backend_time_limits_within_60_seconds', False))
        modules[name] = {'accepted': accepted, 'outcome': result['outcome'],
                         'expected_coverage': count, 'reported_coverage': result['obligations_reported'],
                         'source_match': matched, 'hole_free': hole_free,
                         'all_obligation_statuses_checked': statuses_complete,
                         'recorded_toolchain_and_runtime_match': runtime_matched,
                         'union_syntax_audited': syntax_audited,
                         'backend_limits_ok': result.get('backend_time_limits_within_60_seconds', False),
                         'unproved': result['unproved'], 'result': str(path)}
    # A successful top-level run can still depend on an unchecked or failed
    # imported theorem. Require independently checked, source-matched proofs
    # for every theorem-bearing local import, including transitive imports.
    individual = {name: data['accepted'] for name, data in modules.items()}
    for name, data in modules.items():
        needed = proof_dependencies(base / 'models', name)
        missing = [dep for dep in needed if dep not in individual]
        failed = [dep for dep in needed if dep in individual and not individual[dep]]
        data.update({'individual_module_accepted': individual[name],
                     'required_proof_modules': needed,
                     'missing_dependency_runs': missing,
                     'failed_dependency_runs': failed})
        data['accepted'] = individual[name] and not missing and not failed
    targets = []
    for target in obligations['required_targets']:
        module = target['module']
        exists = bool(module and re.search(r'\bTHEOREM\s+' + re.escape(target['theorem']) + r'\b',
                      code_only((base / 'models' / (module + '.tla')).read_text())))
        targets.append({**target, 'accepted': bool(exists and modules.get(module, {}).get('accepted', False))})
    stages = json.loads((output / 'stages.json').read_text())
    probes = [s for s in stages if s['name'] in
              ('parser_selftest', 'prover_selftest', 'prover_group_selftest', 'source_semantics_selftest')]
    probes_ok = len(probes) == 4 and all(s['returncode'] == 0 for s in probes)
    coverage = stage_coverage(stages)
    stages_ok = coverage['accepted']
    syntax_closure = set().union(*(set(local_closure(base / 'models', m)) for m in PROOF_SYNTAX_ROOTS))
    missing_syntax = sorted(set(modules) - syntax_closure)
    complete = bool(toolchain_ok and not changed and probes_ok and stages_ok and not missing_syntax and all(m['accepted'] for m in modules.values()) and all(t['accepted'] for t in targets))
    result = {'complete_proof': complete, 'status': 'complete' if complete else 'incomplete',
              'source_manifest_sha256': digest(base / 'source-manifest.json'),
              'source_changes_during_run': changed, 'selftests_passed': probes_ok,
              'toolchain_audit_passed': bool(toolchain_ok), 'toolchain_audits': audits,
              'execution_stages_passed': stages_ok,
              'execution_stage_coverage': coverage,
              'proof_modules_without_semantic_preflight': missing_syntax,
              'modules': modules, 'targets': targets, 'stages': stages,
              'tlc_is_not_a_proof': True, 'excluded': obligations['excluded']}
    (output / 'acceptance.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = assess(args.base, args.output)
    print(json.dumps({'status': result['status'], 'open_targets': [t['id'] for t in result['targets'] if not t['accepted']]}))
    raise SystemExit(0 if result['complete_proof'] else 2)
