---------------------- MODULE TRaftLiftedCoreAliases09 ----------------------
EXTENDS TRaftLiftedCoreAliases08b

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasLeaderAppendOnly ==
    LiftedSafety!LeaderAppendOnly = LeaderAppendOnly
BY ONLY ZenonT(10)
   DEF LeaderAppendOnly, LiftedSafety!LeaderAppendOnly

THEOREM LiftedCoreAliasLogMatching ==
    LiftedSafety!LogMatching = LogMatching
BY ONLY ZenonT(10), LiftedCoreAliasPartitions, LiftedCoreAliasPart, LiftedCoreAliasPrefix, LiftedCoreAliasOrigin
   DEF LogMatching, LiftedSafety!LogMatching

THEOREM LiftedCoreAliasCommittedPartitionAgreement ==
    LiftedSafety!CommittedPartitionAgreement = CommittedPartitionAgreement
BY ONLY ZenonT(10)
   DEF CommittedPartitionAgreement, LiftedSafety!CommittedPartitionAgreement

THEOREM LiftedCoreAliasIntraPartitionRankEquivalence ==
    LiftedSafety!IntraPartitionRankEquivalence = IntraPartitionRankEquivalence
BY ONLY ZenonT(10), LiftedCoreAliasCur, LiftedCoreAliasCount, LiftedCoreAliasClosedPrefix, LiftedCoreAliasOrigin, LiftedCoreAliasRank
   DEF IntraPartitionRankEquivalence, LiftedSafety!IntraPartitionRankEquivalence

THEOREM LiftedCoreAliasPartitionLeaderCompleteness ==
    LiftedSafety!PartitionLeaderCompleteness = PartitionLeaderCompleteness
BY ONLY ZenonT(10), LiftedCoreAliasPart
   DEF PartitionLeaderCompleteness, LiftedSafety!PartitionLeaderCompleteness

THEOREM LiftedCoreAliasEntryLeaderCompleteness ==
    LiftedSafety!EntryLeaderCompleteness = EntryLeaderCompleteness
BY ONLY ZenonT(10)
   DEF EntryLeaderCompleteness, LiftedSafety!EntryLeaderCompleteness

THEOREM LiftedCoreAliasStateMachineSafety ==
    LiftedSafety!StateMachineSafety = StateMachineSafety
BY ONLY ZenonT(10)
   DEF StateMachineSafety, LiftedSafety!StateMachineSafety

THEOREM LiftedCoreAliasPartitionStateMachineSafety ==
    LiftedSafety!PartitionStateMachineSafety = PartitionStateMachineSafety
BY ONLY ZenonT(10)
   DEF PartitionStateMachineSafety, LiftedSafety!PartitionStateMachineSafety

THEOREM LiftedCoreAliasApplicationOrder ==
    LiftedSafety!ApplicationOrder = ApplicationOrder
BY ONLY ZenonT(10)
   DEF ApplicationOrder, LiftedSafety!ApplicationOrder

THEOREM LiftedCoreAliasCommittedKnowledgeSound ==
    LiftedSafety!CommittedKnowledgeSound = CommittedKnowledgeSound
BY ONLY ZenonT(10)
   DEF CommittedKnowledgeSound, LiftedSafety!CommittedKnowledgeSound
=============================================================================
