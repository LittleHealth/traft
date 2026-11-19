---------------------- MODULE TRaftPointClientAliases01 ----------------------
EXTENDS TRaftPointCoreAliases08

\* Definition equalities only; no protocol guard or safety assumption.

THEOREM PointClientAliasSeqDomain ==
    PointLift!SeqDomain = SeqDomain
BY ONLY SMT
   DEF SeqDomain, PointLift!SeqDomain

THEOREM PointClientAliasKeys ==
    PointLift!Keys = Keys
BY ONLY SMT
   DEF Keys, PointLift!Keys

THEOREM PointClientAliaslocalClientVars ==
    PointLift!localClientVars = localClientVars
BY ONLY SMT
   DEF localClientVars, PointLift!localClientVars

THEOREM PointClientAliasReturnedIds ==
    PointLift!ReturnedIds = ReturnedIds
BY ONLY SMT
   DEF ReturnedIds, PointLift!ReturnedIds

THEOREM PointClientAliasElectionSafety ==
    PointLift!ElectionSafety = ElectionSafety
BY ONLY SMT
   DEF ElectionSafety, PointLift!ElectionSafety

THEOREM PointClientAliasPartitionCommandsIndependent ==
    PointLift!PartitionCommandsIndependent = PartitionCommandsIndependent
BY ONLY SMT
   DEF PartitionCommandsIndependent, PointLift!PartitionCommandsIndependent

THEOREM PointClientAliasRequestIds ==
    PointLift!RequestIds = RequestIds
BY ONLY SMT, PointClientAliasSeqDomain
   DEF RequestIds, PointLift!RequestIds

THEOREM PointClientAliasClientCommands ==
    PointLift!ClientCommands = ClientCommands
BY ONLY SMT, PointClientAliasRequestIds, PointClientAliasKeys
   DEF ClientCommands, PointLift!ClientCommands

THEOREM PointClientAliasEmptyCache ==
    PointLift!EmptyCache = EmptyCache
BY ONLY SMT, PointClientAliasRequestIds
   DEF EmptyCache, PointLift!EmptyCache

THEOREM PointClientAliasReply ==
    \A db, q : PointLift!Reply(db, q) = Reply(db, q)
BY ONLY SMT
   DEF Reply, PointLift!Reply

THEOREM PointClientAliasEffect ==
    \A db, q : PointLift!Effect(db, q) = Effect(db, q)
BY ONLY ZenonT(10)
   DEF Effect, PointLift!Effect

THEOREM PointClientAliasMustSeparate ==
    \A L, q : PointLift!MustSeparate(L, q) = MustSeparate(L, q)
BY ONLY ZenonT(10)
   DEF MustSeparate, PointLift!MustSeparate, HasRead, PointLift!HasRead, Timestamp, PointLift!Timestamp, Timed, PointLift!Timed, MaxTimestamp, PointLift!MaxTimestamp, Part, PointLift!Part, Cur, PointLift!Cur, MaxOr, PointLift!MaxOr, Count, PointLift!Count, Cardinality, PointLift!Cardinality

THEOREM PointClientAliasReadIsolation ==
    PointLift!ReadIsolation = ReadIsolation
BY ONLY SMT, PointCoreAliasPart
   DEF ReadIsolation, PointLift!ReadIsolation

THEOREM PointClientAliasRequestIdentityState ==
    PointLift!RequestIdentityState = RequestIdentityState
BY ONLY SMT, PointClientAliasClientCommands
   DEF RequestIdentityState, PointLift!RequestIdentityState

THEOREM PointClientAliasCanonicalPointLogs ==
    \A C : PointLift!CanonicalPointLogs(C) = CanonicalPointLogs(C)
BY ONLY SMT, PointCoreAliasTerms, PointClientAliasClientCommands
   DEF CanonicalPointLogs, PointLift!CanonicalPointLogs, PointLog, PointLift!PointLog, Part, PointLift!Part

=============================================================================
