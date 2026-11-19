---------------------- MODULE TRaftPointCoreAliases10 ----------------------
EXTENDS TRaftPointCoreAliases09

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasAppliedEntriesPreserved ==
    PointLift!AppliedEntriesPreserved = AppliedEntriesPreserved
BY ONLY ZenonT(10)
   DEF AppliedEntriesPreserved, PointLift!AppliedEntriesPreserved

THEOREM PointCoreAliasQuorumProposalPreservation ==
    PointLift!QuorumProposalPreservation = QuorumProposalPreservation
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasResult, PointCoreAliasAck
   DEF QuorumProposalPreservation, PointLift!QuorumProposalPreservation

THEOREM PointCoreAliasRecoveryPreservesCommitted ==
    PointLift!RecoveryPreservesCommitted = RecoveryPreservesCommitted
BY ONLY ZenonT(10)
   DEF RecoveryPreservesCommitted, PointLift!RecoveryPreservesCommitted

THEOREM PointCoreAliasRecoveryReportsHaveOrigin ==
    PointLift!RecoveryReportsHaveOrigin = RecoveryReportsHaveOrigin
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasReporters, PointCoreAliasReportedProposals, PointCoreAliasReportedEntries
   DEF RecoveryReportsHaveOrigin, PointLift!RecoveryReportsHaveOrigin

THEOREM PointCoreAliasRecoveryUnionCoherent ==
    PointLift!RecoveryUnionCoherent = RecoveryUnionCoherent
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasCoherent, PointCoreAliasLatest, PointCoreAliasReporters, PointCoreAliasReportedProposals, PointCoreAliasRecovered
   DEF RecoveryUnionCoherent, PointLift!RecoveryUnionCoherent

THEOREM PointCoreAliasRecoveryCandidatesPreserveEvidence ==
    PointLift!RecoveryCandidatesPreserveEvidence = RecoveryCandidatesPreserveEvidence
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasLatest, PointCoreAliasReporters, PointCoreAliasReportedProposals, PointCoreAliasRecovered
   DEF RecoveryCandidatesPreserveEvidence, PointLift!RecoveryCandidatesPreserveEvidence

THEOREM PointCoreAliasCommitEvidenceSound ==
    PointLift!CommitEvidenceSound = CommitEvidenceSound
BY ONLY ZenonT(10), PointCoreAliasEvidence
   DEF CommitEvidenceSound, PointLift!CommitEvidenceSound

THEOREM PointCoreAliasCommitEvidenceAgreement ==
    PointLift!CommitEvidenceAgreement = CommitEvidenceAgreement
BY ONLY ZenonT(10)
   DEF CommitEvidenceAgreement, PointLift!CommitEvidenceAgreement

THEOREM PointCoreAliasCommitNoticeHasQuorum ==
    PointLift!CommitNoticeHasQuorum = CommitNoticeHasQuorum
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasMessageAckers
   DEF CommitNoticeHasQuorum, PointLift!CommitNoticeHasQuorum

THEOREM PointCoreAliasConfirmationHasQuorum ==
    PointLift!ConfirmationHasQuorum = ConfirmationHasQuorum
BY ONLY ZenonT(10), PointCoreAliasQuorum, PointCoreAliasResult, PointCoreAliasAck
   DEF ConfirmationHasQuorum, PointLift!ConfirmationHasQuorum
=============================================================================
