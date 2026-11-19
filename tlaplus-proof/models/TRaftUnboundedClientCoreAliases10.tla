-------------------- MODULE TRaftUnboundedClientCoreAliases10 --------------------
EXTENDS TRaftUnboundedClientCoreAliases09

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasAppliedEntriesPreserved ==
    UnboundedClient!AppliedEntriesPreserved = AppliedEntriesPreserved
BY ONLY ZenonT(10)
   DEF AppliedEntriesPreserved, UnboundedClient!AppliedEntriesPreserved

THEOREM UnboundedClientCoreAliasQuorumProposalPreservation ==
    UnboundedClient!QuorumProposalPreservation = QuorumProposalPreservation
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasResult, UnboundedClientCoreAliasAck
   DEF QuorumProposalPreservation, UnboundedClient!QuorumProposalPreservation

THEOREM UnboundedClientCoreAliasRecoveryPreservesCommitted ==
    UnboundedClient!RecoveryPreservesCommitted = RecoveryPreservesCommitted
BY ONLY ZenonT(10)
   DEF RecoveryPreservesCommitted, UnboundedClient!RecoveryPreservesCommitted

THEOREM UnboundedClientCoreAliasRecoveryReportsHaveOrigin ==
    UnboundedClient!RecoveryReportsHaveOrigin = RecoveryReportsHaveOrigin
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasReporters, UnboundedClientCoreAliasReportedProposals, UnboundedClientCoreAliasReportedEntries
   DEF RecoveryReportsHaveOrigin, UnboundedClient!RecoveryReportsHaveOrigin

THEOREM UnboundedClientCoreAliasRecoveryUnionCoherent ==
    UnboundedClient!RecoveryUnionCoherent = RecoveryUnionCoherent
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasCoherent, UnboundedClientCoreAliasLatest, UnboundedClientCoreAliasReporters, UnboundedClientCoreAliasReportedProposals, UnboundedClientCoreAliasRecovered
   DEF RecoveryUnionCoherent, UnboundedClient!RecoveryUnionCoherent

THEOREM UnboundedClientCoreAliasRecoveryCandidatesPreserveEvidence ==
    UnboundedClient!RecoveryCandidatesPreserveEvidence = RecoveryCandidatesPreserveEvidence
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasLatest, UnboundedClientCoreAliasReporters, UnboundedClientCoreAliasReportedProposals, UnboundedClientCoreAliasRecovered
   DEF RecoveryCandidatesPreserveEvidence, UnboundedClient!RecoveryCandidatesPreserveEvidence

THEOREM UnboundedClientCoreAliasCommitEvidenceSound ==
    UnboundedClient!CommitEvidenceSound = CommitEvidenceSound
BY ONLY ZenonT(10), UnboundedClientCoreAliasEvidence
   DEF CommitEvidenceSound, UnboundedClient!CommitEvidenceSound

THEOREM UnboundedClientCoreAliasCommitEvidenceAgreement ==
    UnboundedClient!CommitEvidenceAgreement = CommitEvidenceAgreement
BY ONLY ZenonT(10)
   DEF CommitEvidenceAgreement, UnboundedClient!CommitEvidenceAgreement

THEOREM UnboundedClientCoreAliasCommitNoticeHasQuorum ==
    UnboundedClient!CommitNoticeHasQuorum = CommitNoticeHasQuorum
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasMessageAckers
   DEF CommitNoticeHasQuorum, UnboundedClient!CommitNoticeHasQuorum

THEOREM UnboundedClientCoreAliasConfirmationHasQuorum ==
    UnboundedClient!ConfirmationHasQuorum = ConfirmationHasQuorum
BY ONLY ZenonT(10), UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasResult, UnboundedClientCoreAliasAck
   DEF ConfirmationHasQuorum, UnboundedClient!ConfirmationHasQuorum
=============================================================================
