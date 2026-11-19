-------------------- MODULE TRaftUnboundedClientHistoryIdentity --------------------
EXTENDS TRaftUnboundedClientSpecificationIdentity

\* Keep the history checker independent of the implementation witness.
\* These are definition identities, proved before the final composition.
THEOREM UnboundedClientCalledIdsIdentity == UnboundedClient!CalledIds = CalledIds
BY ONLY SMT DEF UnboundedClient!CalledIds, CalledIds

THEOREM UnboundedClientFiniteOrdersIdentity ==
    \A S : UnboundedClient!FiniteOrders(S) = FiniteOrders(S)
BY ONLY ZenonT(10)
   DEF UnboundedClient!FiniteOrders, FiniteOrders,
       UnboundedClient!Cardinality, Cardinality,
       UnboundedClient!Enumerates, Enumerates,
       UnboundedClient!SequenceEntries, SequenceEntries,
       UnboundedClient!Seq, Seq, UnboundedClient!Len, Len

THEOREM UnboundedClientRealTimeIdentity ==
    \A order : UnboundedClient!ProofRespectsRealTime(order) <=> ProofRespectsRealTime(order)
BY ONLY ZenonT(10)
   DEF UnboundedClient!ProofRespectsRealTime, ProofRespectsRealTime,
       UnboundedClient!Ids, Ids, UnboundedClient!Position, Position,
       UnboundedClient!Len, Len

THEOREM UnboundedClientFoldExecuteIdentity ==
    \A order, db, answers :
      UnboundedClient!FoldExecuteOrder(order, db, answers) = FoldExecuteOrder(order, db, answers)
BY ONLY ZenonT(10)
   DEF UnboundedClient!FoldExecuteOrder, FoldExecuteOrder,
       UnboundedClient!Fold, Fold, UnboundedClient!FoldTrace, FoldTrace,
       UnboundedClient!SequentialRequestStep, SequentialRequestStep,
       UnboundedClient!Effect, Effect, UnboundedClient!Reply, Reply,
       UnboundedClient!Command, Command, UnboundedClient!Len, Len

THEOREM UnboundedClientHistoryIdentity == FoldHistoryLinearizable <=> UnboundedClient!FoldHistoryLinearizable
BY ONLY ZenonT(10), UnboundedClientCalledIdsIdentity, UnboundedClientFiniteOrdersIdentity,
   UnboundedClientRealTimeIdentity, UnboundedClientFoldExecuteIdentity,
   UnboundedClientEmptyMachineIdentity, UnboundedClientEmptyAnswersIdentity
   DEF FoldHistoryLinearizable, UnboundedClient!FoldHistoryLinearizable
=============================================================================
