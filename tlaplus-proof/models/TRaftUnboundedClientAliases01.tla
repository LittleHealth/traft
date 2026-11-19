---------------------- MODULE TRaftUnboundedClientAliases01 ----------------------
EXTENDS TRaftUnboundedClientCoreAliases11

\* Definition equalities only; no protocol guard or safety assumption.

THEOREM UnboundedClientAliasSeqDomain ==
    UnboundedClient!SeqDomain = SeqDomain
BY ONLY SMT, UnboundedClientConstantSelections
   DEF SeqDomain, UnboundedClient!SeqDomain

THEOREM UnboundedClientAliasKeys ==
    UnboundedClient!Keys = Keys
BY ONLY SMT
   DEF Keys, UnboundedClient!Keys

THEOREM UnboundedClientAliaslocalClientVars ==
    UnboundedClient!localClientVars = localClientVars
BY ONLY SMT
   DEF localClientVars, UnboundedClient!localClientVars

THEOREM UnboundedClientAliasReturnedIds ==
    UnboundedClient!ReturnedIds = ReturnedIds
BY ONLY SMT
   DEF ReturnedIds, UnboundedClient!ReturnedIds

THEOREM UnboundedClientAliasElectionSafety ==
    UnboundedClient!ElectionSafety = ElectionSafety
BY ONLY SMT
   DEF ElectionSafety, UnboundedClient!ElectionSafety

THEOREM UnboundedClientAliasPartitionCommandsIndependent ==
    UnboundedClient!PartitionCommandsIndependent = PartitionCommandsIndependent
BY ONLY SMT
   DEF PartitionCommandsIndependent, UnboundedClient!PartitionCommandsIndependent

THEOREM UnboundedClientAliasRequestIds ==
    UnboundedClient!RequestIds = RequestIds
BY ONLY SMT, UnboundedClientAliasSeqDomain
   DEF RequestIds, UnboundedClient!RequestIds

THEOREM UnboundedClientAliasClientCommands ==
    UnboundedClient!ClientCommands = ClientCommands
BY ONLY SMT, UnboundedClientAliasRequestIds, UnboundedClientAliasKeys
   DEF ClientCommands, UnboundedClient!ClientCommands

THEOREM UnboundedClientAliasEmptyCache ==
    UnboundedClient!EmptyCache = EmptyCache
BY ONLY SMT, UnboundedClientAliasRequestIds
   DEF EmptyCache, UnboundedClient!EmptyCache

THEOREM UnboundedClientAliasReply ==
    \A db, q : UnboundedClient!Reply(db, q) = Reply(db, q)
BY ONLY SMT
   DEF Reply, UnboundedClient!Reply

THEOREM UnboundedClientAliasEffect ==
    \A db, q : UnboundedClient!Effect(db, q) = Effect(db, q)
BY ONLY ZenonT(10)
   DEF Effect, UnboundedClient!Effect

THEOREM UnboundedClientAliasMustSeparate ==
    \A L, q : UnboundedClient!MustSeparate(L, q) = MustSeparate(L, q)
BY ONLY ZenonT(10)
   DEF MustSeparate, UnboundedClient!MustSeparate, HasRead, UnboundedClient!HasRead, Timestamp, UnboundedClient!Timestamp, Timed, UnboundedClient!Timed, MaxTimestamp, UnboundedClient!MaxTimestamp, Part, UnboundedClient!Part, Cur, UnboundedClient!Cur, MaxOr, UnboundedClient!MaxOr, Count, UnboundedClient!Count, Cardinality, UnboundedClient!Cardinality

THEOREM UnboundedClientAliasReadIsolation ==
    UnboundedClient!ReadIsolation = ReadIsolation
BY ONLY SMT, UnboundedClientCoreAliasPart
   DEF ReadIsolation, UnboundedClient!ReadIsolation



=============================================================================
