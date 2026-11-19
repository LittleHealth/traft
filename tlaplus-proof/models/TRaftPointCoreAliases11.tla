---------------------- MODULE TRaftPointCoreAliases11 ----------------------
EXTENDS TRaftPointCoreAliases10

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasAckDurability ==
    PointLift!AckDurability = AckDurability
BY ONLY ZenonT(10)
   DEF AckDurability, PointLift!AckDurability

THEOREM PointCoreAliasEvidenceRespectsPartitionOrder ==
    PointLift!EvidenceRespectsPartitionOrder = EvidenceRespectsPartitionOrder
BY ONLY ZenonT(10)
   DEF EvidenceRespectsPartitionOrder, PointLift!EvidenceRespectsPartitionOrder

THEOREM PointCoreAliasNormalCountCheckSound ==
    PointLift!NormalCountCheckSound = NormalCountCheckSound
BY ONLY ZenonT(10), PointCoreAliasPrefix, PointCoreAliasCanReceive
   DEF NormalCountCheckSound, PointLift!NormalCountCheckSound

THEOREM PointCoreAliasEntryContextUnique ==
    PointLift!EntryContextUnique = EntryContextUnique
BY ONLY ZenonT(10)
   DEF EntryContextUnique, PointLift!EntryContextUnique

THEOREM PointCoreAliasSafety ==
    PointLift!Safety = Safety
BY ONLY ZenonT(10), PointCoreAliasTypeOK, PointCoreAliasElectionSafety, PointCoreAliasLeaderAppendOnly, PointCoreAliasLogMatching, PointCoreAliasCommittedPartitionAgreement, PointCoreAliasIntraPartitionRankEquivalence, PointCoreAliasPartitionLeaderCompleteness, PointCoreAliasEntryLeaderCompleteness, PointCoreAliasStateMachineSafety, PointCoreAliasPartitionStateMachineSafety, PointCoreAliasApplicationOrder, PointCoreAliasCommittedKnowledgeSound, PointCoreAliasAppliedEntriesPreserved, PointCoreAliasQuorumProposalPreservation, PointCoreAliasRecoveryPreservesCommitted, PointCoreAliasRecoveryReportsHaveOrigin, PointCoreAliasRecoveryUnionCoherent, PointCoreAliasRecoveryCandidatesPreserveEvidence, PointCoreAliasCommitEvidenceSound, PointCoreAliasCommitEvidenceAgreement, PointCoreAliasCommitNoticeHasQuorum, PointCoreAliasConfirmationHasQuorum, PointCoreAliasAckDurability, PointCoreAliasEvidenceRespectsPartitionOrder, PointCoreAliasNormalCountCheckSound, PointCoreAliasEntryContextUnique
   DEF Safety, PointLift!Safety
=============================================================================
