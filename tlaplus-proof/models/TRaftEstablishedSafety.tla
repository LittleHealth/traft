----------------------- MODULE TRaftEstablishedSafety -----------------------
EXTENDS TRaftElectionTemporal, TRaftCommitTemporal, TRaftApplicationOrderProof,
        TRaftClientRefinementProof

\* This named subset is NOT the full 26-conjunct Safety predicate. Each member
\* has an independent temporal proof with no assumption of candidate Inv.
EstablishedSafety == /\ ElectionSafety /\ ApplicationOrder
                     /\ CommittedKnowledgeSound /\ ConfirmationHasQuorum
                     /\ AckDurability /\ CommitEvidenceSound

THEOREM ProtocolEstablishedSafety == Spec => []EstablishedSafety
<1>1. Spec => []ElectionSafety
    BY ProtocolElectionSafety
<1>2. Spec => []ApplicationOrder
    BY PTL, ProtocolApplicationOrder DEF OrderInvariant
<1>3. Spec => [](CommittedKnowledgeSound /\ ConfirmationHasQuorum)
    BY ProtocolCommitKnowledgeSound
<1>4. Spec => []AckDurability
    BY PTL, ProtocolAckDurability DEF DurabilityInvariant
<1>5. Spec => []CommitEvidenceSound
    BY ProtocolIndependentEvidence
<1> QED BY PTL, <1>1, <1>2, <1>3, <1>4, <1>5 DEF EstablishedSafety

THEOREM ClientEstablishedSafety ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []EstablishedSafety
<1>1. ClientSpecification(Extra) => Spec
    BY ClientTemporalRefinement
<1> QED BY PTL, <1>1, ProtocolEstablishedSafety
=============================================================================
