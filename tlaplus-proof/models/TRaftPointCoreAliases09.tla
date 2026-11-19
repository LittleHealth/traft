---------------------- MODULE TRaftPointCoreAliases09 ----------------------
EXTENDS TRaftPointCoreAliases08b

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasLeaderAppendOnly ==
    PointLift!LeaderAppendOnly = LeaderAppendOnly
BY ONLY ZenonT(10)
   DEF LeaderAppendOnly, PointLift!LeaderAppendOnly

THEOREM PointCoreAliasLogMatching ==
    PointLift!LogMatching = LogMatching
BY ONLY ZenonT(10), PointCoreAliasPartitions, PointCoreAliasPart, PointCoreAliasPrefix, PointCoreAliasOrigin
   DEF LogMatching, PointLift!LogMatching

THEOREM PointCoreAliasCommittedPartitionAgreement ==
    PointLift!CommittedPartitionAgreement = CommittedPartitionAgreement
BY ONLY ZenonT(10)
   DEF CommittedPartitionAgreement, PointLift!CommittedPartitionAgreement

THEOREM PointCoreAliasIntraPartitionRankEquivalence ==
    PointLift!IntraPartitionRankEquivalence = IntraPartitionRankEquivalence
BY ONLY ZenonT(10), PointCoreAliasCur, PointCoreAliasCount, PointCoreAliasClosedPrefix, PointCoreAliasOrigin, PointCoreAliasRank
   DEF IntraPartitionRankEquivalence, PointLift!IntraPartitionRankEquivalence

THEOREM PointCoreAliasPartitionLeaderCompleteness ==
    PointLift!PartitionLeaderCompleteness = PartitionLeaderCompleteness
BY ONLY ZenonT(10), PointCoreAliasPart
   DEF PartitionLeaderCompleteness, PointLift!PartitionLeaderCompleteness

THEOREM PointCoreAliasEntryLeaderCompleteness ==
    PointLift!EntryLeaderCompleteness = EntryLeaderCompleteness
BY ONLY ZenonT(10)
   DEF EntryLeaderCompleteness, PointLift!EntryLeaderCompleteness

THEOREM PointCoreAliasStateMachineSafety ==
    PointLift!StateMachineSafety = StateMachineSafety
BY ONLY ZenonT(10)
   DEF StateMachineSafety, PointLift!StateMachineSafety

THEOREM PointCoreAliasPartitionStateMachineSafety ==
    PointLift!PartitionStateMachineSafety = PartitionStateMachineSafety
BY ONLY ZenonT(10)
   DEF PartitionStateMachineSafety, PointLift!PartitionStateMachineSafety

THEOREM PointCoreAliasApplicationOrder ==
    PointLift!ApplicationOrder = ApplicationOrder
BY ONLY ZenonT(10)
   DEF ApplicationOrder, PointLift!ApplicationOrder

THEOREM PointCoreAliasCommittedKnowledgeSound ==
    PointLift!CommittedKnowledgeSound = CommittedKnowledgeSound
BY ONLY ZenonT(10)
   DEF CommittedKnowledgeSound, PointLift!CommittedKnowledgeSound
=============================================================================
