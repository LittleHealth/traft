-------------------- MODULE TRaftUnboundedCoreAliases09 --------------------
EXTENDS TRaftUnboundedCoreAliases08b

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasLeaderAppendOnly ==
    UnboundedCore!LeaderAppendOnly = LeaderAppendOnly
BY ONLY ZenonT(10)
   DEF LeaderAppendOnly, UnboundedCore!LeaderAppendOnly

THEOREM UnboundedCoreAliasLogMatching ==
    UnboundedCore!LogMatching = LogMatching
BY ONLY ZenonT(10), UnboundedCoreAliasPartitions, UnboundedCoreAliasPart, UnboundedCoreAliasPrefix, UnboundedCoreAliasOrigin
   DEF LogMatching, UnboundedCore!LogMatching

THEOREM UnboundedCoreAliasCommittedPartitionAgreement ==
    UnboundedCore!CommittedPartitionAgreement = CommittedPartitionAgreement
BY ONLY ZenonT(10)
   DEF CommittedPartitionAgreement, UnboundedCore!CommittedPartitionAgreement

THEOREM UnboundedCoreAliasIntraPartitionRankEquivalence ==
    UnboundedCore!IntraPartitionRankEquivalence = IntraPartitionRankEquivalence
BY ONLY ZenonT(10), UnboundedCoreAliasCur, UnboundedCoreAliasCount, UnboundedCoreAliasClosedPrefix, UnboundedCoreAliasOrigin, UnboundedCoreAliasRank
   DEF IntraPartitionRankEquivalence, UnboundedCore!IntraPartitionRankEquivalence

THEOREM UnboundedCoreAliasPartitionLeaderCompleteness ==
    UnboundedCore!PartitionLeaderCompleteness = PartitionLeaderCompleteness
BY ONLY ZenonT(10), UnboundedCoreAliasPart
   DEF PartitionLeaderCompleteness, UnboundedCore!PartitionLeaderCompleteness

THEOREM UnboundedCoreAliasEntryLeaderCompleteness ==
    UnboundedCore!EntryLeaderCompleteness = EntryLeaderCompleteness
BY ONLY ZenonT(10)
   DEF EntryLeaderCompleteness, UnboundedCore!EntryLeaderCompleteness

THEOREM UnboundedCoreAliasStateMachineSafety ==
    UnboundedCore!StateMachineSafety = StateMachineSafety
BY ONLY ZenonT(10)
   DEF StateMachineSafety, UnboundedCore!StateMachineSafety

THEOREM UnboundedCoreAliasPartitionStateMachineSafety ==
    UnboundedCore!PartitionStateMachineSafety = PartitionStateMachineSafety
BY ONLY ZenonT(10)
   DEF PartitionStateMachineSafety, UnboundedCore!PartitionStateMachineSafety

THEOREM UnboundedCoreAliasApplicationOrder ==
    UnboundedCore!ApplicationOrder = ApplicationOrder
BY ONLY ZenonT(10)
   DEF ApplicationOrder, UnboundedCore!ApplicationOrder

THEOREM UnboundedCoreAliasCommittedKnowledgeSound ==
    UnboundedCore!CommittedKnowledgeSound = CommittedKnowledgeSound
BY ONLY ZenonT(10)
   DEF CommittedKnowledgeSound, UnboundedCore!CommittedKnowledgeSound
=============================================================================
