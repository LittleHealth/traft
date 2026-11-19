# Independent evidence and cross-term recovery

## Evidence versus knowledge

Commit evidence is computed from issued ACKs by distinct replicas with one owner and authorizing epoch. Entry creation terms survive recovery and differ from ACK authorization terms. ACK delivery updates knowledge; commit notifications and recovery confirmations cannot manufacture independent evidence. Duplicates do not create additional replicas, and late messages cannot combine terms.

[TRaftDurabilityProof](../models/TRaftDurabilityProof.tla), [TRaftAckSourceProof](../models/TRaftAckSourceProof.tla), and [TRaftCommitTemporal](../models/TRaftCommitTemporal.tla) connect evidence to durable data and actual sources.

## Sound count boundaries

The boundary test compares the preceding partition's total, committed, and locally stored distinct-entry counts. The proof first establishes a common recovery origin and coherent creation context, then that the follower's valid entries are a subset of the partition. Only with these premises does finite cardinality equality imply complete content equality. See [TRaftBoundaryProof](../models/TRaftBoundaryProof.tla) and [TRaftFiniteLogProof](../models/TRaftFiniteLogProof.tla).

## Recovery interpretation

`BuildRecovery` inherits the latest complete retained recovery result, including a durable proposal with unknown confirmation. `Latest` orders proposals by the creation term and partition index of their opening no-op. For a selected proposal `p`, with faults disabled, `Recovered(c,p)` is `Result(p) ∪ {e ∈ ReportedEntries(c) : e.term = p.first.term ∧ e.part ≥ p.first.part}`. Reported entries include installed logs and complete retained recovery results. Reports at different ordinary-partition progress contribute extensions at and beyond the selected origin's partition. Entry identities, indices, creation terms, partition indices, and contents are retained. The empty-origin branch requires empty reported entries.

The [revised Appendix A](../../supplementary/README.md) states this rule explicitly. Its notation and the corresponding model definitions are mapped in [paper correspondence](paper-correspondence.md).

Retaining a proposal differs from installing its result as active history. Installation, confirmation, and activation have separately proved source conditions. Recovery synchronizes the recovered prefix and new-term no-op with a quorum before serving ordinary writes. Higher terms can interrupt these stages.

## Preserving earlier certificates

For entry `e` and authorization term `t`, consider already-issued ACK replicas together with replicas that have not advanced beyond `t`. The proof establishes a decreasing upper bound on replicas still able to complete an old-term certificate. It then applies quorum intersection with actual election/recovery certificates and report provenance.

The argument covers evidence formed before recovery and old-term evidence completed later. It connects a still relevant old entry to an actual durable source, then to the selected origin and compatible union. It never infers an actual old ACK solely from the possibility of a future ACK. See [TRaftPotentialProof](../models/TRaftPotentialProof.tla), [TRaftRecoveryMergeProof](../models/TRaftRecoveryMergeProof.tla), and [TRaftRecoveryInduction](../models/TRaftRecoveryInduction.tla).

The resulting invariants imply `RecoveryCandidatesPreserveEvidence`, `QuorumProposalPreservation`, and `RecoveryPreservesCommitted`. Full induction connects them to global Safety; recovery does not assume those conclusions as guards.

Completed checks cover partial replication, retained unconfirmed proposals, different ordinary progress, interrupted recovery, uncommitted rollback, and a fixed recovery prefix followed by every three-step suffix. Exact bounds are in [the published check manifest](../manifests/published-checks.json).
