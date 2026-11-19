---------------------- MODULE TRaftLiftedCoreAliases10 ----------------------
EXTENDS TRaftLiftedCoreAliases09

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasAppliedEntriesPreserved ==
    LiftedSafety!AppliedEntriesPreserved = AppliedEntriesPreserved
BY ONLY ZenonT(10)
   DEF AppliedEntriesPreserved, LiftedSafety!AppliedEntriesPreserved

THEOREM LiftedCoreAliasQuorumProposalPreservation ==
    LiftedSafety!QuorumProposalPreservation = QuorumProposalPreservation
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasResult, LiftedCoreAliasAck
   DEF QuorumProposalPreservation, LiftedSafety!QuorumProposalPreservation

THEOREM LiftedCoreAliasRecoveryPreservesCommitted ==
    LiftedSafety!RecoveryPreservesCommitted = RecoveryPreservesCommitted
BY ONLY ZenonT(10)
   DEF RecoveryPreservesCommitted, LiftedSafety!RecoveryPreservesCommitted

THEOREM LiftedCoreAliasRecoveryReportsHaveOrigin ==
    LiftedSafety!RecoveryReportsHaveOrigin = RecoveryReportsHaveOrigin
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasReporters, LiftedCoreAliasReportedProposals, LiftedCoreAliasReportedEntries
   DEF RecoveryReportsHaveOrigin, LiftedSafety!RecoveryReportsHaveOrigin

THEOREM LiftedCoreAliasRecoveryUnionCoherent ==
    LiftedSafety!RecoveryUnionCoherent = RecoveryUnionCoherent
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasCoherent, LiftedCoreAliasLatest, LiftedCoreAliasReporters, LiftedCoreAliasReportedProposals, LiftedCoreAliasRecovered
   DEF RecoveryUnionCoherent, LiftedSafety!RecoveryUnionCoherent

THEOREM LiftedCoreAliasRecoveryCandidatesPreserveEvidence ==
    LiftedSafety!RecoveryCandidatesPreserveEvidence = RecoveryCandidatesPreserveEvidence
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasLatest, LiftedCoreAliasReporters, LiftedCoreAliasReportedProposals, LiftedCoreAliasRecovered
   DEF RecoveryCandidatesPreserveEvidence, LiftedSafety!RecoveryCandidatesPreserveEvidence

THEOREM LiftedCoreAliasCommitEvidenceSound ==
    LiftedSafety!CommitEvidenceSound = CommitEvidenceSound
BY ONLY ZenonT(10), LiftedCoreAliasEvidence
   DEF CommitEvidenceSound, LiftedSafety!CommitEvidenceSound

THEOREM LiftedCoreAliasCommitEvidenceAgreement ==
    LiftedSafety!CommitEvidenceAgreement = CommitEvidenceAgreement
BY ONLY ZenonT(10)
   DEF CommitEvidenceAgreement, LiftedSafety!CommitEvidenceAgreement

THEOREM LiftedCoreAliasCommitNoticeHasQuorum ==
    LiftedSafety!CommitNoticeHasQuorum = CommitNoticeHasQuorum
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasMessageAckers
   DEF CommitNoticeHasQuorum, LiftedSafety!CommitNoticeHasQuorum

THEOREM LiftedCoreAliasConfirmationHasQuorum ==
    LiftedSafety!ConfirmationHasQuorum = ConfirmationHasQuorum
BY ONLY ZenonT(10), LiftedCoreAliasQuorum, LiftedCoreAliasResult, LiftedCoreAliasAck
   DEF ConfirmationHasQuorum, LiftedSafety!ConfirmationHasQuorum
=============================================================================
