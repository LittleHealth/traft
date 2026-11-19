-------------------- MODULE TRaftUnboundedClientCoreAliases09 --------------------
EXTENDS TRaftUnboundedClientCoreAliases08b

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasLeaderAppendOnly ==
    UnboundedClient!LeaderAppendOnly = LeaderAppendOnly
BY ONLY ZenonT(10)
   DEF LeaderAppendOnly, UnboundedClient!LeaderAppendOnly

THEOREM UnboundedClientCoreAliasLogMatching ==
    UnboundedClient!LogMatching = LogMatching
BY ONLY ZenonT(10), UnboundedClientCoreAliasPartitions, UnboundedClientCoreAliasPart, UnboundedClientCoreAliasPrefix, UnboundedClientCoreAliasOrigin
   DEF LogMatching, UnboundedClient!LogMatching

THEOREM UnboundedClientCoreAliasCommittedPartitionAgreement ==
    UnboundedClient!CommittedPartitionAgreement = CommittedPartitionAgreement
BY ONLY ZenonT(10)
   DEF CommittedPartitionAgreement, UnboundedClient!CommittedPartitionAgreement

THEOREM UnboundedClientCoreAliasIntraPartitionRankEquivalence ==
    UnboundedClient!IntraPartitionRankEquivalence = IntraPartitionRankEquivalence
BY ONLY ZenonT(10), UnboundedClientCoreAliasCur, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasClosedPrefix, UnboundedClientCoreAliasOrigin, UnboundedClientCoreAliasRank
   DEF IntraPartitionRankEquivalence, UnboundedClient!IntraPartitionRankEquivalence

THEOREM UnboundedClientCoreAliasPartitionLeaderCompleteness ==
    UnboundedClient!PartitionLeaderCompleteness = PartitionLeaderCompleteness
BY ONLY ZenonT(10), UnboundedClientCoreAliasPart
   DEF PartitionLeaderCompleteness, UnboundedClient!PartitionLeaderCompleteness

THEOREM UnboundedClientCoreAliasEntryLeaderCompleteness ==
    UnboundedClient!EntryLeaderCompleteness = EntryLeaderCompleteness
BY ONLY ZenonT(10)
   DEF EntryLeaderCompleteness, UnboundedClient!EntryLeaderCompleteness

THEOREM UnboundedClientCoreAliasStateMachineSafety ==
    UnboundedClient!StateMachineSafety = StateMachineSafety
BY ONLY ZenonT(10)
   DEF StateMachineSafety, UnboundedClient!StateMachineSafety

THEOREM UnboundedClientCoreAliasPartitionStateMachineSafety ==
    UnboundedClient!PartitionStateMachineSafety = PartitionStateMachineSafety
BY ONLY ZenonT(10)
   DEF PartitionStateMachineSafety, UnboundedClient!PartitionStateMachineSafety

THEOREM UnboundedClientCoreAliasApplicationOrder ==
    UnboundedClient!ApplicationOrder = ApplicationOrder
BY ONLY ZenonT(10)
   DEF ApplicationOrder, UnboundedClient!ApplicationOrder

THEOREM UnboundedClientCoreAliasCommittedKnowledgeSound ==
    UnboundedClient!CommittedKnowledgeSound = CommittedKnowledgeSound
BY ONLY ZenonT(10)
   DEF CommittedKnowledgeSound, UnboundedClient!CommittedKnowledgeSound
=============================================================================
