------------------------- MODULE TRaftSafetyEvidenceOrder --------------------
EXTENDS TRaftEvidenceOrderProof

\* Prime only the closed implication; each post-state premise is a separate
\* obligation in SafetyClosureInductiveStep, not the conclusion of this leaf.
THEOREM EvidenceRespectsPartitionOrderInductiveStep ==
    ASSUME ProofInvariant', CommitEvidenceSound', EntryContextUnique'
    PROVE EvidenceRespectsPartitionOrder'
<1>1. CandidateImpliesEvidenceOrder'
    BY ONLY PTL, CandidateImpliesEvidenceOrder
<1> QED BY <1>1
=============================================================================
