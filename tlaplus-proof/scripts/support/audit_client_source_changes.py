#!/usr/bin/env python3
"""Audit the exact observer refactor and local capacity-boundary repair."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


OLD_BOUNDARY = 'MustSeparate(L, q) == q.op = "Get" \\/ HasRead(L) \\/ Timestamp(q) <= MaxTimestamp(L)\n'
NEW_BOUNDARY = OLD_BOUNDARY.rstrip('\n') + '\n                       \\/ Count(L, Cur(L)) = MaxPartitionSize\n'


def admission_delta(before, after):
    """Accept precisely one additional local full-partition alternative."""
    return before.count(OLD_BOUNDARY) == 1 and before.replace(OLD_BOUNDARY, NEW_BOUNDARY) == after


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    baseline = HERE / 'baseline'
    models = HERE / 'models'
    old = (baseline / 'TRaftClients-before-shared-observer.tla').read_text()
    after = (models / 'TRaftClients.tla').read_text()
    moved = '''ClientNext == ClientAction /\\ Observe /\\ ObserveLinearization
ClientSpec == ClientSpecification(ObserveLinearization)
ProjectsToProtocol == [][Next]_vars

'''
    renamed = '''\\* Historical recursive observer retained for differential checks. The live
\\* observer and ClientSpec are inherited from the shared specification.
RecursiveObserveLinearization =='''
    expected = old.replace('EXTENDS TRaftClientCore', 'EXTENDS TRaftSharedClientSpecification')
    expected = expected.replace('ObserveLinearization ==', renamed).replace(moved, '')
    old_core = (baseline / 'TRaftClientCore-before-shared-observer.tla').read_bytes()
    core = (models / 'TRaftClientCore.tla').read_bytes()
    capacity_delta = admission_delta(old_core.decode(), core.decode())
    accepted = old.count(moved) == 1 and expected == after and capacity_delta
    report = {
        'accepted': accepted,
        'before_client_sha256': digest(old.encode()),
        'after_client_sha256': digest(after.encode()),
        'before_client_core_sha256': digest(old_core),
        'after_client_core_sha256': digest(core),
        'physical_client_actions_unchanged': old_core == core,
        'exact_local_capacity_boundary_delta': capacity_delta,
        'all_other_client_core_source_unchanged': capacity_delta,
        'admission_change': 'A full current partition opens a successor for the arriving data command; '
                            'the previous client rule omitted this case.',
        'admission_semantic_targets': ['TRaftClientAdmissionProof.CapacityBoundaryStartsSuccessor',
                                       'TRaftClientAdmissionProof.ExistingAdmissionsArePreserved'],
        'paper_rule': 'main.tex equation def-partition-index: theta_current = Theta starts a new partition.',
        'independent_recursive_checks_preserved': expected == after,
        'preserved_checks': ['HistoryLinearizable', 'WitnessValid', 'ClientSafety'],
        'preserved_reference_algorithms': ['Incorporate', 'Orders', 'ExecuteOrder'],
        'observer_change': 'ClientSpec inherits the Fold observer from the shared specification; '
                           'the old observer is retained as RecursiveObserveLinearization.',
        'semantic_target': 'TRaftClientSpecificationProof.SharedClientSpecificationIdentity',
        'limitations': 'Exact source delta only. The capacity change adds client behavior and requires '
                       'fresh proofs; this is not equivalence to the old admission rule or to the '
                       'historical recursive observer.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    return 0 if accepted else 1


if __name__ == '__main__':
    raise SystemExit(main())
