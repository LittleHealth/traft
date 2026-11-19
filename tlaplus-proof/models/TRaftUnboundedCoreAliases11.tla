-------------------- MODULE TRaftUnboundedCoreAliases11 --------------------
EXTENDS TRaftUnboundedCoreAliases10

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasAckDurability ==
    UnboundedCore!AckDurability = AckDurability
BY ONLY ZenonT(10)
   DEF AckDurability, UnboundedCore!AckDurability

THEOREM UnboundedCoreAliasEvidenceRespectsPartitionOrder ==
    UnboundedCore!EvidenceRespectsPartitionOrder = EvidenceRespectsPartitionOrder
BY ONLY ZenonT(10)
   DEF EvidenceRespectsPartitionOrder, UnboundedCore!EvidenceRespectsPartitionOrder

THEOREM UnboundedCoreAliasNormalCountCheckSound ==
    UnboundedCore!NormalCountCheckSound = NormalCountCheckSound
BY ONLY ZenonT(10), UnboundedCoreAliasPrefix, UnboundedCoreAliasCanReceive
   DEF NormalCountCheckSound, UnboundedCore!NormalCountCheckSound

THEOREM UnboundedCoreAliasEntryContextUnique ==
    UnboundedCore!EntryContextUnique = EntryContextUnique
BY ONLY ZenonT(10)
   DEF EntryContextUnique, UnboundedCore!EntryContextUnique

THEOREM UnboundedCoreAliasSafety ==
    UnboundedCore!Safety = Safety
BY ONLY ZenonT(10), UnboundedCoreAliasTypeOK, UnboundedCoreAliasElectionSafety, UnboundedCoreAliasLeaderAppendOnly, UnboundedCoreAliasLogMatching, UnboundedCoreAliasCommittedPartitionAgreement, UnboundedCoreAliasIntraPartitionRankEquivalence, UnboundedCoreAliasPartitionLeaderCompleteness, UnboundedCoreAliasEntryLeaderCompleteness, UnboundedCoreAliasStateMachineSafety, UnboundedCoreAliasPartitionStateMachineSafety, UnboundedCoreAliasApplicationOrder, UnboundedCoreAliasCommittedKnowledgeSound, UnboundedCoreAliasAppliedEntriesPreserved, UnboundedCoreAliasQuorumProposalPreservation, UnboundedCoreAliasRecoveryPreservesCommitted, UnboundedCoreAliasRecoveryReportsHaveOrigin, UnboundedCoreAliasRecoveryUnionCoherent, UnboundedCoreAliasRecoveryCandidatesPreserveEvidence, UnboundedCoreAliasCommitEvidenceSound, UnboundedCoreAliasCommitEvidenceAgreement, UnboundedCoreAliasCommitNoticeHasQuorum, UnboundedCoreAliasConfirmationHasQuorum, UnboundedCoreAliasAckDurability, UnboundedCoreAliasEvidenceRespectsPartitionOrder, UnboundedCoreAliasNormalCountCheckSound, UnboundedCoreAliasEntryContextUnique
   DEF Safety, UnboundedCore!Safety
=============================================================================
