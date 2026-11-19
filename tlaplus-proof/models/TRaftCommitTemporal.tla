-------------------------- MODULE TRaftCommitTemporal ------------------------
EXTENDS TRaftCommitFrames, TRaftCommitActions, TRaftDurabilityProof, TRaftControlTemporal

\* Formal theorem instance: the two relevant mutation switches are off.
ASSUME CommitProofFaultsDisabled == CommitFaultsDisabled
USE CommitProofFaultsDisabled DEF CommitProofFaultsDisabled, CommitFaultsDisabled

THEOREM KnowledgeInductiveStep ==
    ASSUME ElectionInvariant, ControlInvariant, DurabilityInvariant,
           KnowledgeInvariant, CommitFaultsDisabled, Next
    PROVE KnowledgeInvariant'
<1>1. ackMessages \subseteq ackMessages' /\ commitHistory \subseteq commitHistory'
      /\ ProtocolNext /\ Observe
    <2>1. DurableData /\ ProtocolNext /\ Observe
        BY DEF Next, DurabilityInvariant
    <2>2. DurabilityStep
        BY EveryStepPreservesDurabilityFacts, <2>1
    <2>3. commitHistory' = commitHistory \cup Evidence(ackMessages')
        BY <2>1 DEF Observe
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3 DEF DurabilityStep
<1>2. AckInboxOrigins'
    BY EveryStepPreservesInboxOrigins, <1>1 DEF KnowledgeInvariant
<1>3. KnowledgeChangingNext \/ UNCHANGED <<knownCommitted, commitMessages, confirmations>>
    BY ProtocolKnowledgeProjection, <1>1
<1>4. KnowledgeShape' /\ CommittedKnowledgeSound' /\ CommitMessageEvidence'
    BY SMT, <1>1, <1>3, CommitEntryPreservesKnowledge,
       LearnCommitPreservesKnowledge, AdvertiseCommitPreservesKnowledge,
       KnowledgeEvidencePersists
       DEF KnowledgeChangingNext, ConfirmProposal, KnowledgeInvariant
<1>5. ConfirmationHasQuorum'
    BY SMT, <1>1, <1>3, ConfirmProposalPreservesCertificate, ConfirmationEvidencePersists
       DEF KnowledgeChangingNext, KnowledgeInvariant, CommitFaultsDisabled,
           CommitEntry, AdvertiseCommit, LearnCommit
<1> QED BY <1>2, <1>4, <1>5 DEF KnowledgeInvariant

THEOREM ProtocolCommitKnowledge ==
    Spec => []KnowledgeInvariant
<1>1. Spec => []ElectionInvariant /\ []ControlInvariant /\ []DurabilityInvariant
    BY PTL, ElectionInvariantAlways, ControlInvariantAlways, ProtocolAckDurability
<1>2. Init => KnowledgeInvariant
    BY KnowledgeInitially
<1>3. ElectionInvariant /\ ControlInvariant /\ DurabilityInvariant /\ KnowledgeInvariant
      /\ [Next]_vars => KnowledgeInvariant'
    BY SMT, KnowledgeInductiveStep, KnowledgeStuttering
       DEF vars, protocolVars, observerVars, KnowledgeVars, CommitFaultsDisabled
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec

THEOREM ProtocolCommitKnowledgeSound ==
    Spec => [](CommittedKnowledgeSound /\ ConfirmationHasQuorum)
BY PTL, ProtocolCommitKnowledge DEF KnowledgeInvariant
=============================================================================
