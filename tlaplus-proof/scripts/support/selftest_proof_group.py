#!/usr/bin/env python3
"""Exercise real positive/negative and shared-import proof groups on dq-179."""
import argparse
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent / 'models'))
from run_proof_group import run_group
from run_proofs import RUNTIME_PROFILES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--models', type=Path, required=True)
    parser.add_argument('--tlapm', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--runtime-profile', choices=RUNTIME_PROFILES, default='standard')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    runner = SimpleNamespace(source=[args.models.resolve()], tlapm=args.tlapm.resolve(),
                             output=args.output / 'results', timeout=300,
                             runtime_profile=args.runtime_profile,
                             modules=['ProofToolNegative', 'ProofToolSMTNegative', 'ProofToolPositive'])
    negative = run_group(runner)
    rows = {r['module']: json.loads(Path(r['result']).read_text()) for r in negative['modules']}
    bad, smt_bad, good = rows['ProofToolNegative'], rows['ProofToolSMTNegative'], rows['ProofToolPositive']
    negative_ok = (negative['returncode'] == 0 and negative['termination'] is None
                   and not negative['all_modules_proved']
                   and bad['outcome'] == 'unproved' and bad['obligations_expected'] == 2
                   and any(s.get('status') == 'failed' and s.get('reason') == 'false'
                           and s.get('prover') == 'isabelle'
                           for s in bad['unproved'].values())
                   and smt_bad['outcome'] == 'unproved' and smt_bad['obligations_expected'] == 2
                   and any(s.get('status') == 'failed' and s.get('reason') == 'false'
                           and s.get('prover') == 'smt'
                           for s in smt_bad['unproved'].values())
                   and good['outcome'] == 'proved' and good['obligations_expected'] == 4
                   and all(r['backend_time_limits_within_60_seconds'] for r in rows.values()))
    # Both counts were established independently by single-module runs. The
    # second module imports the first, so this also tests coverage when the
    # same lemma is an explicitly checked target and another target's import.
    runner.modules = ['TRaftSequenceFoldProof', 'TRaftFoldSimulation']
    positive = run_group(runner)
    positive_ok = (positive['all_modules_proved']
                   and {r['module']: r['obligations_expected'] for r in positive['modules']}
                       == {'TRaftSequenceFoldProof': 124, 'TRaftFoldSimulation': 112})
    result = {'accepted': negative_ok and positive_ok,
              'negative_group_detected_false_obligation': negative_ok,
              'arithmetic_and_smt_negative_controls_required': True,
              'shared_import_group_checked_both_modules': positive_ok,
              'negative_group': negative['group_id'], 'positive_group': positive['group_id'],
              'positive_group_seconds': positive['elapsed_seconds'],
              'proof_cache_reused': False, 'full_proof_complete': False}
    (args.output / 'group-selftest.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
    return 0 if result['accepted'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
