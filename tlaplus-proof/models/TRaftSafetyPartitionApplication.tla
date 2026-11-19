---------------------- MODULE TRaftSafetyPartitionApplication ----------------------
EXTENDS TRaftCertifiedPartitionProof

THEOREM PartitionStateMachineSafetyInductiveStep ==
    ASSUME ProofInvariant', CommitEvidenceSound', EntryContextUnique'
    PROVE PartitionStateMachineSafety'
<1>1. CandidateAppliedPartitionsAgree'
    BY ONLY PTL, CandidateAppliedPartitionsAgree
<1> QED BY <1>1
=============================================================================
