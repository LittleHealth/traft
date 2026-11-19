-------------------- MODULE TRaftUnboundedClientCoreAliases11 --------------------
EXTENDS TRaftUnboundedClientCoreAliases10

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasAckDurability ==
    UnboundedClient!AckDurability = AckDurability
BY ONLY ZenonT(10)
   DEF AckDurability, UnboundedClient!AckDurability

THEOREM UnboundedClientCoreAliasEvidenceRespectsPartitionOrder ==
    UnboundedClient!EvidenceRespectsPartitionOrder = EvidenceRespectsPartitionOrder
BY ONLY ZenonT(10)
   DEF EvidenceRespectsPartitionOrder, UnboundedClient!EvidenceRespectsPartitionOrder

THEOREM UnboundedClientCoreAliasNormalCountCheckSound ==
    UnboundedClient!NormalCountCheckSound = NormalCountCheckSound
BY ONLY ZenonT(10), UnboundedClientCoreAliasPrefix, UnboundedClientCoreAliasCanReceive
   DEF NormalCountCheckSound, UnboundedClient!NormalCountCheckSound

THEOREM UnboundedClientCoreAliasEntryContextUnique ==
    UnboundedClient!EntryContextUnique = EntryContextUnique
BY ONLY ZenonT(10)
   DEF EntryContextUnique, UnboundedClient!EntryContextUnique

THEOREM UnboundedClientCoreAliasSafety ==
    UnboundedClient!Safety = Safety
BY ONLY ZenonT(10), UnboundedClientCoreAliasTypeOK, UnboundedClientCoreAliasElectionSafety, UnboundedClientCoreAliasLeaderAppendOnly, UnboundedClientCoreAliasLogMatching, UnboundedClientCoreAliasCommittedPartitionAgreement, UnboundedClientCoreAliasIntraPartitionRankEquivalence, UnboundedClientCoreAliasPartitionLeaderCompleteness, UnboundedClientCoreAliasEntryLeaderCompleteness, UnboundedClientCoreAliasStateMachineSafety, UnboundedClientCoreAliasPartitionStateMachineSafety, UnboundedClientCoreAliasApplicationOrder, UnboundedClientCoreAliasCommittedKnowledgeSound, UnboundedClientCoreAliasAppliedEntriesPreserved, UnboundedClientCoreAliasQuorumProposalPreservation, UnboundedClientCoreAliasRecoveryPreservesCommitted, UnboundedClientCoreAliasRecoveryReportsHaveOrigin, UnboundedClientCoreAliasRecoveryUnionCoherent, UnboundedClientCoreAliasRecoveryCandidatesPreserveEvidence, UnboundedClientCoreAliasCommitEvidenceSound, UnboundedClientCoreAliasCommitEvidenceAgreement, UnboundedClientCoreAliasCommitNoticeHasQuorum, UnboundedClientCoreAliasConfirmationHasQuorum, UnboundedClientCoreAliasAckDurability, UnboundedClientCoreAliasEvidenceRespectsPartitionOrder, UnboundedClientCoreAliasNormalCountCheckSound, UnboundedClientCoreAliasEntryContextUnique
   DEF Safety, UnboundedClient!Safety
=============================================================================
