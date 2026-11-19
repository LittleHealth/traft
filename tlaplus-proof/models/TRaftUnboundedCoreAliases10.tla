-------------------- MODULE TRaftUnboundedCoreAliases10 --------------------
EXTENDS TRaftUnboundedCoreAliases09

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasAppliedEntriesPreserved ==
    UnboundedCore!AppliedEntriesPreserved = AppliedEntriesPreserved
BY ONLY ZenonT(10)
   DEF AppliedEntriesPreserved, UnboundedCore!AppliedEntriesPreserved

THEOREM UnboundedCoreAliasQuorumProposalPreservation ==
    UnboundedCore!QuorumProposalPreservation = QuorumProposalPreservation
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasResult, UnboundedCoreAliasAck
   DEF QuorumProposalPreservation, UnboundedCore!QuorumProposalPreservation

THEOREM UnboundedCoreAliasRecoveryPreservesCommitted ==
    UnboundedCore!RecoveryPreservesCommitted = RecoveryPreservesCommitted
BY ONLY ZenonT(10)
   DEF RecoveryPreservesCommitted, UnboundedCore!RecoveryPreservesCommitted

THEOREM UnboundedCoreAliasRecoveryReportsHaveOrigin ==
    UnboundedCore!RecoveryReportsHaveOrigin = RecoveryReportsHaveOrigin
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasReporters, UnboundedCoreAliasReportedProposals, UnboundedCoreAliasReportedEntries
   DEF RecoveryReportsHaveOrigin, UnboundedCore!RecoveryReportsHaveOrigin

THEOREM UnboundedCoreAliasRecoveryUnionCoherent ==
    UnboundedCore!RecoveryUnionCoherent = RecoveryUnionCoherent
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasCoherent, UnboundedCoreAliasLatest, UnboundedCoreAliasReporters, UnboundedCoreAliasReportedProposals, UnboundedCoreAliasRecovered
   DEF RecoveryUnionCoherent, UnboundedCore!RecoveryUnionCoherent

THEOREM UnboundedCoreAliasRecoveryCandidatesPreserveEvidence ==
    UnboundedCore!RecoveryCandidatesPreserveEvidence = RecoveryCandidatesPreserveEvidence
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasLatest, UnboundedCoreAliasReporters, UnboundedCoreAliasReportedProposals, UnboundedCoreAliasRecovered
   DEF RecoveryCandidatesPreserveEvidence, UnboundedCore!RecoveryCandidatesPreserveEvidence

THEOREM UnboundedCoreAliasCommitEvidenceSound ==
    UnboundedCore!CommitEvidenceSound = CommitEvidenceSound
BY ONLY ZenonT(10), UnboundedCoreAliasEvidence
   DEF CommitEvidenceSound, UnboundedCore!CommitEvidenceSound

THEOREM UnboundedCoreAliasCommitEvidenceAgreement ==
    UnboundedCore!CommitEvidenceAgreement = CommitEvidenceAgreement
BY ONLY ZenonT(10)
   DEF CommitEvidenceAgreement, UnboundedCore!CommitEvidenceAgreement

THEOREM UnboundedCoreAliasCommitNoticeHasQuorum ==
    UnboundedCore!CommitNoticeHasQuorum = CommitNoticeHasQuorum
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasMessageAckers
   DEF CommitNoticeHasQuorum, UnboundedCore!CommitNoticeHasQuorum

THEOREM UnboundedCoreAliasConfirmationHasQuorum ==
    UnboundedCore!ConfirmationHasQuorum = ConfirmationHasQuorum
BY ONLY ZenonT(10), UnboundedCoreAliasQuorum, UnboundedCoreAliasResult, UnboundedCoreAliasAck
   DEF ConfirmationHasQuorum, UnboundedCore!ConfirmationHasQuorum
=============================================================================
