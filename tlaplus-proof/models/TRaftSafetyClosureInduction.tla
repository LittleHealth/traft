--------------------- MODULE TRaftSafetyClosureInduction ---------------------
EXTENDS TRaftSafetyEntryContexts, TRaftSafetyPartitionAgreement, TRaftSafetyPartitionLeader, TRaftSafetyPartitionApplication, TRaftSafetyAppliedPreservation, TRaftSafetyCommitNotice, TRaftSafetyEvidenceOrder,
        TRaftInvariantDefinitions, TRaftSafetyConsequences,
        TRaftAppendOnlyProof, TRaftHistoryOriginProof
USE FormalFaultsDisabled DEF FormalFaultsDisabled

THEOREM ElectionStateConsequence == ElectionInvariant => ElectionSafety
BY ElectionInvariantImpliesElectionSafety

\* No post-state safety premise is assumed. The seven explicit leaves below
\* must be proved before the conditionally derived targets can be accepted.
THEOREM SafetyClosureInductiveStep ==
    ASSUME Inv, ProofNext, ProofInvariant'
    PROVE Safety'
<1>1. TypeOK' /\ ElectionInvariant'
      /\ CommittedKnowledgeSound' /\ ConfirmationHasQuorum' /\ AckDurability'
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       KnowledgeInvariant, DurabilityInvariant
<1>2. ElectionStateConsequence'
    BY ONLY PTL, ElectionStateConsequence
<1>3. ElectionSafety'
    BY ONLY <1>1, <1>2
<1>4. CommitEvidenceSound'
    BY EvidenceInductiveStep DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>5. LeaderAppendOnly'
    BY LeaderAppendOnlyInductiveStep DEF Inv, Safety, ProofNext
<1>6. ApplicationOrder'
    <2>1. applied \in [Replicas -> SUBSET Entries]
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. AppliedShape
        BY ONLY SMT, <2>1 DEF AppliedShape
    <2> QED BY OrderInductiveStep, <2>2 DEF Inv, Safety, ProofNext, OrderInvariant
<1>7. EntryContextUnique'
    BY EntryContextUniqueInductiveStep
<1>70. DerivedSafety'
    BY CandidateSafetyConsequencesNext, <1>4, <1>7
<1>8. CommittedPartitionAgreement'
    BY CommittedPartitionAgreementInductiveStep, <1>4, <1>7
<1>9. PartitionLeaderCompleteness'
    BY PartitionLeaderCompletenessInductiveStep, <1>4, <1>7
<1>10. PartitionStateMachineSafety'
    BY PartitionStateMachineSafetyInductiveStep, <1>4, <1>7
<1>11. AppliedEntriesPreserved'
    BY AppliedEntriesPreservedInductiveStep, <1>4, <1>7
<1>12. CommitNoticeHasQuorum'
    BY CommitNoticeHasQuorumInductiveStep
<1>13. EvidenceRespectsPartitionOrder'
    BY EvidenceRespectsPartitionOrderInductiveStep, <1>4, <1>7
<1> QED BY ONLY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
    <1>10, <1>11, <1>12, <1>13, <1>70 DEF Safety, DerivedSafety
=============================================================================
