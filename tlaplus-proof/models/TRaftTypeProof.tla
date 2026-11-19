----------------------------- MODULE TRaftTypeProof ---------------------------
EXTENDS TRaftInvariantDefinitions, TRaftLogTypeProof, TRaftTermAndVoteProof,
        TRaftDurabilityProof, TRaftCommitTemporal
USE FormalFaultsDisabled DEF FormalFaultsDisabled, CommitFaultsDisabled

THEOREM AliveTypeInductiveStep ==
    ASSUME alive \in [Replicas -> BOOLEAN], ProtocolNext
    PROVE alive' \in [Replicas -> BOOLEAN]
<1>0. alive \in [Replicas -> BOOLEAN]
    OBVIOUS
<1>1. (\E r \in Replicas : Crash(r) \/ Restart(r)) \/ UNCHANGED alive
    BY AliveActionProjection
<1>2. \A r \in Replicas : (Crash(r) \/ Restart(r)) =>
          (alive' = [alive EXCEPT ![r] = FALSE] \/ alive' = [alive EXCEPT ![r] = TRUE])
    BY SMT DEF Crash, Restart
<1>3. \A r \in Replicas : [alive EXCEPT ![r] = FALSE] \in [Replicas -> BOOLEAN]
                           /\ [alive EXCEPT ![r] = TRUE] \in [Replicas -> BOOLEAN]
    BY ONLY SMT, <1>0
<1> QED BY ONLY ZenonT(5), <1>0, <1>1, <1>2, <1>3

THEOREM TypeOKInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE TypeOK'
<1>1. ProofInvariant /\ CommitEvidenceSound /\ ProtocolNext /\ Next
      /\ ElectionInvariant /\ ControlInvariant /\ DurabilityInvariant /\ KnowledgeInvariant
    BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, ProofNext, Next
<1>2. ElectionInvariant' /\ ControlInvariant' /\ DurabilityInvariant' /\ KnowledgeInvariant'
    BY ElectionInductiveStep, ControlInductiveStep, DurabilityInductiveStep, KnowledgeInductiveStep, <1>1
<1>3. LogStorageTypes' /\ ProposalEntryTypes'
    BY LogTypesInductiveStep, <1>1
<1>4. alive' \in [Replicas -> BOOLEAN]
    BY AliveTypeInductiveStep, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>5. appendOnlyOK' \in BOOLEAN /\ applicationOrderOK' \in BOOLEAN
    BY SMT DEF Inv, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       ProofNext, Next, Observe
<1> QED BY SMT, <1>2, <1>3, <1>4, <1>5 DEF TypeOK, LogStorageTypes, ProposalEntryTypes, ValidProposalEntry,
    ElectionInvariant, ElectionTypes, ControlInvariant, ControlShape, DurabilityInvariant,
    DurableData, FormalStored, RetainedStored, KnowledgeInvariant, AckInboxOrigins
=============================================================================
