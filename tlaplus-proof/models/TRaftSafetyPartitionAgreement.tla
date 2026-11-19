---------------------- MODULE TRaftSafetyPartitionAgreement ----------------------
EXTENDS TRaftCertifiedPartitionProof

THEOREM CommittedPartitionAgreementInductiveStep ==
    ASSUME ProofInvariant', CommitEvidenceSound', EntryContextUnique'
    PROVE CommittedPartitionAgreement'
<1>1. CandidateCommittedPartitionsAgree'
    BY ONLY PTL, CandidateCommittedPartitionsAgree
<1> QED BY <1>1
=============================================================================
