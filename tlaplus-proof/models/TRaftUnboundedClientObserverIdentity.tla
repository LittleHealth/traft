-------------------- MODULE TRaftUnboundedClientObserverIdentity --------------------
EXTENDS TRaftUnboundedClientStateAliases

THEOREM UnboundedClientObserverIdentity ==
    UnboundedClient!ObserveLinearization <=> ObserveLinearization
BY ONLY ZenonT(10)
   DEF ObserveLinearization, UnboundedClient!ObserveLinearization, ProofObserveLinearization, UnboundedClient!ProofObserveLinearization, SortedIncorporation, UnboundedClient!SortedIncorporation, SortedEntryOrder, UnboundedClient!SortedEntryOrder, EntryOrders, UnboundedClient!EntryOrders, Enumerates, UnboundedClient!Enumerates, IncreasingEntryOrder, UnboundedClient!IncreasingEntryOrder, SequenceEntries, UnboundedClient!SequenceEntries, Fold, UnboundedClient!Fold, FoldTrace, UnboundedClient!FoldTrace, LinearizationEntryStep, UnboundedClient!LinearizationEntryStep, Ids, UnboundedClient!Ids, Effect, UnboundedClient!Effect, Reply, UnboundedClient!Reply, Cardinality, UnboundedClient!Cardinality, IsFiniteSet, UnboundedClient!IsFiniteSet
=============================================================================
