----------------------- MODULE TRaftSafetyCommitNotice ------------------------
EXTENDS TRaftCommitNoticeProof

THEOREM CommitNoticeSafetyStep ==
    (Inv /\ ProofNext) => CommitNoticeHasQuorum'
BY CommitNoticeHasQuorumInductiveStep
=============================================================================
