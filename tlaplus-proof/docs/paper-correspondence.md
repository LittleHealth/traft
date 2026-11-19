# Paper, model, and theorem correspondence

The [supplementary PDF](../../supplementary/appendix.pdf) preserves the original published main paper on pages 1–14. Appendix A, beginning on page 15, was clarified on 20 November 2026; its [LaTeX source](../../supplementary/appendix-body.tex) and [revision provenance](../../supplementary/appendix-revision.json) are included. Labels below identify the corresponding manuscript sections/equation. The frozen source audit continues to identify the original proof inputs and the original publication; the revision record identifies the current appendix and PDF. No TLA+ model, proof source, or recorded check changed.

| Paper location | Formal interpretation and actions | Checked consequence |
| --- | --- | --- |
| Log Partition, `eq:def-partition-index` | `CreateEntry`, `CreateSuccessor`; client `MustSeparate`/`Admit` implement timestamp and capacity choices; term changes open a recovery boundary | Canonical log shape, partition invariants, application commutativity |
| Leader Replication, `subsubsec:traft-leader-replication` | `NormalMessage`/`SendEntry` carry identity, partition, and preceding-partition counts | Message provenance and boundary count invariants |
| Follower Processing, `subsubsec:traft-follower-processing` | `CanReceive`, `ReceiveEntry`, `AckEntry`: persist before ACK; require total=committed=local distinct count at a boundary | `NormalCountCheckSound`, `AckDurability` |
| Leader Commitment, `subsubsec:traft-leader-commitment` | `CommitEntry`, `AdvertiseCommit`, `LearnCommit`, `ApplyEntry`; independent `Evidence` derives only from issued ACKs | Commit evidence/knowledge soundness and partition order |
| Leader Election, `subsec:traft-leader-election` | `StartElection`, `GrantVote`, `DeliverVote`, `WinElection`; lexicographic `(last term, partition, count)` rank | Election Safety and unique creation contexts |
| Recovery after Election, `subsubsec:traft-recovery` | `MakeReport`, `BuildRecovery`, `RetainProposal`, `AckProposal`, `ConfirmProposal`, `Activate` | Preservation of prior and potentially later-completed old-term evidence |
| Appendix A, “Precise recovery semantics” | `Latest`, `ReportedEntries`, `Recovered`, and `BuildRecovery` define the selected durable origin and its reported extensions | The appendix's set expression is the fault-free `Recovered` definition |
| Properties: `prop:log-matching`, `prop:leader-completeness`, `prop:state-machine-safety` | Whole-history invariants, provenance, and independent certificate preservation | The corresponding Safety components below and the global `ProtocolSafety` theorem |
| Client extension defined by this artifact | `Invoke`, `Admit`, `ApplyClient`, `SendReply`, `ReceiveReply`; logged singleton `Get`, durable deduplication | Application agreement and `FoldHistoryLinearizable`; not attributed to an unspecified manuscript API |

## Explicit interpretation conditions

Normal boundaries are installed directly when the count rule holds. An ordinary successor does not require a separate recovery-proposal confirmation round; its own commitment still requires a current-term majority of durable ACKs and commitment of preceding partitions. Quorum confirmation of an exact retained recovery result is used for election recovery. The revised Log Matching sketch states these separate conditions explicitly.

The precise recovery rule is:

1. Collect reports from a majority, including the candidate, after reporters adopt the candidate's term. Each report supplies its installed log and complete retained recovery proposals, including proposals whose confirmation is unknown.
2. Select `p` from `Latest(ReportedProposals(c))`. `Latest` orders proposals lexicographically by `(p.first.term, p.first.part)`. A complete result is `Result(p) = p.prefix ∪ {p.first}`; `RetainProposal` requires that result to be durable.
3. Let `U = ReportedEntries(c)`, the union of reported installed logs and complete retained recovery results. Preserve `Result(p)` in full and add `{e ∈ U : e.term = p.first.term ∧ e.part ≥ p.first.part}`. The partition comparison includes ordinary progress beyond the selected proposal's opening partition. If no proposal is reported, `BuildRecovery` permits the empty-result branch only when no entries are reported either.
4. Append a new-term no-op at the next index in the next partition. Copying may be interrupted; retaining and acknowledging the proposal require the entire result to be durable. The candidate installs after majority acknowledgment, commits in partition order, and activates only after the complete result is committed.

The appendix notation maps directly to the model: `B(p)` is `Result(p)`, `t_p` is `p.first.term`, `ρ_p` is `p.first.part`, and `L` is `Recovered(c,p)`, with fault-injection switches disabled. Entry identities, indices, creation terms, partition indices, and contents are preserved. The Leader Completeness sketch now refers to retained recovery origins and reported extensions: an ordinary partition has no separate opening recovery proposal, and the protocol creates at most one recovery proposal per term. See [recovery safety](recovery-safety.md).

Buffer reuse, disk scheduling, and in-flight windows are abstracted away. Time-triggered partition closure is represented nondeterministically; the model does not establish timing or throughput guarantees. The client layer instantiates the point-operation partition rules and adds logged reads. No implementation refinement claim follows from this correspondence table.

## All 26 Safety components

These are direct consequence or preservation entry points. Their premises are discharged by initialization, step preservation, stuttering, and history transport. A conditional lemma alone is not the global safety theorem. All listed proof modules are independently checked in [the result index](../results/proof-modules.json).

| Safety component | Direct theorem | Module |
| --- | --- | --- |
| `TypeOK` | `TypeOKInductiveStep` | [TRaftTypeProof](../models/TRaftTypeProof.tla) |
| `ElectionSafety` | `ElectionStateConsequence` | [TRaftSafetyClosureInduction](../models/TRaftSafetyClosureInduction.tla) |
| `LeaderAppendOnly` | `LeaderAppendOnlyInductiveStep` | [TRaftAppendOnlyProof](../models/TRaftAppendOnlyProof.tla) |
| `LogMatching` | `ContextOriginsImplyLogMatching` | [TRaftLogMatchingFromInvariant](../models/TRaftLogMatchingFromInvariant.tla) |
| `CommittedPartitionAgreement` | `CommittedPartitionAgreementInductiveStep` | [TRaftSafetyPartitionAgreement](../models/TRaftSafetyPartitionAgreement.tla) |
| `IntraPartitionRankEquivalence` | `LogMatchingImpliesRankEquivalence` | [TRaftLogMatchingFromInvariant](../models/TRaftLogMatchingFromInvariant.tla) |
| `PartitionLeaderCompleteness` | `PartitionLeaderCompletenessInductiveStep` | [TRaftSafetyPartitionLeader](../models/TRaftSafetyPartitionLeader.tla) |
| `EntryLeaderCompleteness` | `CandidateImpliesEntryLeaderCompleteness` | [TRaftAgreementFromInvariant](../models/TRaftAgreementFromInvariant.tla) |
| `StateMachineSafety` | `CandidateWithAppliedEvidenceImpliesStateMachineSafety` | [TRaftAgreementFromInvariant](../models/TRaftAgreementFromInvariant.tla) |
| `PartitionStateMachineSafety` | `PartitionStateMachineSafetyInductiveStep` | [TRaftSafetyPartitionApplication](../models/TRaftSafetyPartitionApplication.tla) |
| `ApplicationOrder` | `OrderInductiveStep` | [TRaftApplicationOrderProof](../models/TRaftApplicationOrderProof.tla) |
| `CommittedKnowledgeSound` | `KnowledgeInductiveStep` | [TRaftCommitTemporal](../models/TRaftCommitTemporal.tla) |
| `AppliedEntriesPreserved` | `AppliedEntriesPreservedInductiveStep` | [TRaftSafetyAppliedPreservation](../models/TRaftSafetyAppliedPreservation.tla) |
| `RecoveryUnionCoherent` | `RecoveryMergeCoherentFromInvariant` | [TRaftRecoveryMergeProof](../models/TRaftRecoveryMergeProof.tla) |
| `RecoveryCandidatesPreserveEvidence` | `CandidateRecoveryRetainsEvidence` | [TRaftAgreementFromInvariant](../models/TRaftAgreementFromInvariant.tla) |
| `RecoveryReportsHaveOrigin` | `CandidateReportsHaveOrigin` | [TRaftSafetyConsequences](../models/TRaftSafetyConsequences.tla) |
| `QuorumProposalPreservation` | `CandidateImpliesQuorumProposalPreservation` | [TRaftSafetyConsequences](../models/TRaftSafetyConsequences.tla) |
| `RecoveryPreservesCommitted` | `CandidateImpliesRecoveryPreservesCommitted` | [TRaftAgreementFromInvariant](../models/TRaftAgreementFromInvariant.tla) |
| `CommitEvidenceSound` | `EvidenceInductiveStep` | [TRaftDurabilityProof](../models/TRaftDurabilityProof.tla) |
| `CommitEvidenceAgreement` | `CandidateImpliesEvidenceAgreement` | [TRaftAgreementFromInvariant](../models/TRaftAgreementFromInvariant.tla) |
| `CommitNoticeHasQuorum` | `CommitNoticeHasQuorumInductiveStep` | [TRaftCommitNoticeProof](../models/TRaftCommitNoticeProof.tla) |
| `ConfirmationHasQuorum` | `KnowledgeInductiveStep` | [TRaftCommitTemporal](../models/TRaftCommitTemporal.tla) |
| `AckDurability` | `DurabilityInductiveStep` | [TRaftDurabilityProof](../models/TRaftDurabilityProof.tla) |
| `EvidenceRespectsPartitionOrder` | `EvidenceRespectsPartitionOrderInductiveStep` | [TRaftSafetyEvidenceOrder](../models/TRaftSafetyEvidenceOrder.tla) |
| `NormalCountCheckSound` | `CountSafetyFromCandidate` | [TRaftBoundaryProof](../models/TRaftBoundaryProof.tla) |
| `EntryContextUnique` | `EntryContextUniqueInductiveStep` | [TRaftSafetyEntryContexts](../models/TRaftSafetyEntryContexts.tla) |

Protocol `StateMachineSafety` concerns applied-entry identities; [application agreement](application-consistency.md) additionally establishes point-store state and result agreement.
