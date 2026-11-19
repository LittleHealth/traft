----------------------- MODULE TRaftClientEvidenceInputs ---------------------
EXTENDS TRaftPartitionEvidenceProof, TRaftPointPartitionProof, TRaftFiniteSupport

THEOREM IssuedEntriesAreFinite ==
    ASSUME ProofInvariant
    PROVE IsFiniteSet(IssuedEntries)
<1>1. IsFiniteSet(ackMessages) /\ CanonicalFinite /\ AckOrigin
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       FiniteLogInvariant, FiniteChannels
<1>2. \A a \in ackMessages : IsFiniteSet(a.contents)
    BY FiniteSubset, <1>1 DEF AckOrigin, CanonicalFinite
<1> QED BY ONLY FiniteImageUnion, <1>1, <1>2, IsaM("blast") DEF IssuedEntries

THEOREM EvidenceEntriesAreFiniteAndTyped ==
    ASSUME ProofInvariant, CommitEvidenceSound
    PROVE IsFiniteSet(EvidenceEntries) /\ EvidenceEntries \subseteq Entries
<1>1. IsFiniteSet(IssuedEntries) /\ EvidenceEntries \subseteq IssuedEntries
    BY IssuedEntriesAreFinite, EvidenceIsPossible DEF EvidenceEntries
<1>2. IssuedEntries \subseteq Entries
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       AckOrigin, CanonicalShape, IssuedEntries
<1> QED BY FiniteSubset, <1>1, <1>2

THEOREM TwoEvidenceEntriesShareTypedCanonical ==
    ASSUME ProofInvariant, CommitEvidenceSound,
           NEW e \in EvidenceEntries, NEW f \in EvidenceEntries
    PROVE \E t \in Terms : e \in canonical[t] /\ f \in canonical[t]
<1>1. PICK a \in commitHistory : a.entry = e
    BY DEF EvidenceEntries
<1>2. PICK b \in commitHistory : b.entry = f
    BY DEF EvidenceEntries
<1> QED BY TwoEvidenceEntriesHaveCommonCanonical, <1>1, <1>2

THEOREM EvidenceEntriesAreCoherent ==
    ASSUME ProofInvariant, CommitEvidenceSound
    PROVE Coherent(EvidenceEntries)
<1>1. \A e, f \in EvidenceEntries :
          \E t \in Terms : e \in canonical[t] /\ f \in canonical[t]
    BY TwoEvidenceEntriesShareTypedCanonical
<1>2. \A t \in Terms : Coherent(canonical[t])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>1, <1>2 DEF Coherent

THEOREM EvidenceEntriesRespectPointPartitions ==
    ASSUME ProofInvariant, CommitEvidenceSound,
           \A t \in Terms : PointLog(canonical[t])
    PROVE PointLog(EvidenceEntries)
<1>1. \A e, f \in EvidenceEntries :
          \E t \in Terms : e \in canonical[t] /\ f \in canonical[t]
    BY TwoEvidenceEntriesShareTypedCanonical
<1>2. \A e \in EvidenceEntries : \E t \in Terms : e \in canonical[t]
    BY <1>1
<1> QED BY SMT, <1>1, <1>2 DEF PointLog, Part

THEOREM EvidenceDataHasAnActualCall ==
    ASSUME ProofInvariant, CommitEvidenceSound,
           \A t \in Terms : \A e \in canonical[t] : e.kind = "data" => e.value \in calls
    PROVE \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
<1>1. \A e \in EvidenceEntries : \E t \in Terms : e \in canonical[t]
    BY TwoEvidenceEntriesShareTypedCanonical
<1> QED BY <1>1
=============================================================================
