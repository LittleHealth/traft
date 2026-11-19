---------------------- MODULE TRaftLiftedCoreAliases11 ----------------------
EXTENDS TRaftLiftedCoreAliases10

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasAckDurability ==
    LiftedSafety!AckDurability = AckDurability
BY ONLY ZenonT(10)
   DEF AckDurability, LiftedSafety!AckDurability

THEOREM LiftedCoreAliasEvidenceRespectsPartitionOrder ==
    LiftedSafety!EvidenceRespectsPartitionOrder = EvidenceRespectsPartitionOrder
BY ONLY ZenonT(10)
   DEF EvidenceRespectsPartitionOrder, LiftedSafety!EvidenceRespectsPartitionOrder

THEOREM LiftedCoreAliasNormalCountCheckSound ==
    LiftedSafety!NormalCountCheckSound = NormalCountCheckSound
BY ONLY ZenonT(10), LiftedCoreAliasPrefix, LiftedCoreAliasCanReceive
   DEF NormalCountCheckSound, LiftedSafety!NormalCountCheckSound

THEOREM LiftedCoreAliasEntryContextUnique ==
    LiftedSafety!EntryContextUnique = EntryContextUnique
BY ONLY ZenonT(10)
   DEF EntryContextUnique, LiftedSafety!EntryContextUnique

THEOREM LiftedCoreAliasSafety ==
    LiftedSafety!Safety = Safety
BY ONLY ZenonT(10), LiftedCoreAliasTypeOK, LiftedCoreAliasElectionSafety, LiftedCoreAliasLeaderAppendOnly, LiftedCoreAliasLogMatching, LiftedCoreAliasCommittedPartitionAgreement, LiftedCoreAliasIntraPartitionRankEquivalence, LiftedCoreAliasPartitionLeaderCompleteness, LiftedCoreAliasEntryLeaderCompleteness, LiftedCoreAliasStateMachineSafety, LiftedCoreAliasPartitionStateMachineSafety, LiftedCoreAliasApplicationOrder, LiftedCoreAliasCommittedKnowledgeSound, LiftedCoreAliasAppliedEntriesPreserved, LiftedCoreAliasQuorumProposalPreservation, LiftedCoreAliasRecoveryPreservesCommitted, LiftedCoreAliasRecoveryReportsHaveOrigin, LiftedCoreAliasRecoveryUnionCoherent, LiftedCoreAliasRecoveryCandidatesPreserveEvidence, LiftedCoreAliasCommitEvidenceSound, LiftedCoreAliasCommitEvidenceAgreement, LiftedCoreAliasCommitNoticeHasQuorum, LiftedCoreAliasConfirmationHasQuorum, LiftedCoreAliasAckDurability, LiftedCoreAliasEvidenceRespectsPartitionOrder, LiftedCoreAliasNormalCountCheckSound, LiftedCoreAliasEntryContextUnique
   DEF Safety, LiftedSafety!Safety
=============================================================================
