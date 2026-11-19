---------------------- MODULE TRaftSafetyPartitionLeader ----------------------
EXTENDS TRaftPartitionLeaderProof

THEOREM PartitionLeaderCompletenessInductiveStep ==
    ASSUME ProofInvariant', CommitEvidenceSound', EntryContextUnique'
    PROVE PartitionLeaderCompleteness'
<1>1. CandidatePartitionLeaderCompleteness'
    BY ONLY PTL, CandidatePartitionLeaderCompleteness
<1> QED BY <1>1
=============================================================================
