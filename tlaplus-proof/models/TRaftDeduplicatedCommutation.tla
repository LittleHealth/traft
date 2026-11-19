--------------------- MODULE TRaftDeduplicatedCommutation --------------------
EXTENDS TRaftApplicationProof, TRaftClientPersistenceProof, TRaftFunctionProof

PointStates == [db : [Keys -> Values \cup {Missing}],
                cache : [RequestIds -> [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]]
PointTransition(s, q) ==
    IF s.cache[q.id].ready THEN s
    ELSE [db |-> Effect(s.db, q),
          cache |-> [s.cache EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]]

THEOREM PointTransitionIsTyped ==
    ASSUME NEW s \in PointStates, NEW q \in ClientCommands
    PROVE PointTransition(s, q) \in PointStates
BY SMT DEF PointStates, PointTransition, ClientCommands, Effect, Reply

THEOREM PointTransitionKeepsOtherRequests ==
    ASSUME NEW s \in PointStates, NEW p \in ClientCommands, NEW q \in ClientCommands,
           p.id # q.id
    PROVE PointTransition(s, p).cache[q.id] = s.cache[q.id]
BY SMT DEF PointStates, PointTransition, ClientCommands

THEOREM IndependentRequestIdentities ==
    ASSUME RequestIdentityState, NEW p \in calls, NEW q \in calls, p.key # q.key
    PROVE p.id # q.id
BY SMT DEF RequestIdentityState

THEOREM DistinctFunctionUpdatesCommute ==
    ASSUME NEW N, NEW F, F = [i \in N |-> F[i]], NEW a \in N, NEW b \in N,
           a # b, NEW x, NEW y
    PROVE [[F EXCEPT ![a] = x] EXCEPT ![b] = y]
        = [[F EXCEPT ![b] = y] EXCEPT ![a] = x]
<1>1. DEFINE U == [[F EXCEPT ![a] = x] EXCEPT ![b] = y]
            V == [[F EXCEPT ![b] = y] EXCEPT ![a] = x]
<1>2. [F EXCEPT ![a] = x] = [i \in N |-> [F EXCEPT ![a] = x][i]]
      /\ [F EXCEPT ![b] = y] = [i \in N |-> [F EXCEPT ![b] = y][i]]
    BY FunctionUpdatePreservesDomainShape
<1>3. U = [i \in N |-> U[i]] /\ V = [i \in N |-> V[i]]
    BY FunctionUpdatePreservesDomainShape, <1>2 DEF U, V
<1>4. \A i \in N : U[i] = V[i]
    BY SMT DEF U, V
<1> QED BY ONLY <1>3, <1>4, Isa DEF U, V

THEOREM DeduplicatedPointTransitionsCommute ==
    ASSUME NEW s \in PointStates, NEW p \in ClientCommands, NEW q \in ClientCommands,
           p.id # q.id, p.key # q.key
    PROVE PointTransition(PointTransition(s, p), q) = PointTransition(PointTransition(s, q), p)
<1>1. PointTransition(s, p) \in PointStates /\ PointTransition(s, q) \in PointStates
      /\ PointTransition(s, p).cache[q.id] = s.cache[q.id]
      /\ PointTransition(s, q).cache[p.id] = s.cache[p.id]
    BY PointTransitionIsTyped, PointTransitionKeepsOtherRequests
<1>2. Effect(Effect(s.db, p), q) = Effect(Effect(s.db, q), p)
      /\ Reply(Effect(s.db, p), q) = Reply(s.db, q)
      /\ Reply(Effect(s.db, q), p) = Reply(s.db, p)
    BY IndependentPointEffectsCommute DEF PointStates
<1>3. CASE s.cache[p.id].ready
    BY SMT, <1>1, <1>3 DEF PointTransition
<1>4. CASE s.cache[q.id].ready
    BY SMT, <1>1, <1>4 DEF PointTransition
<1>5. CASE ~s.cache[p.id].ready /\ ~s.cache[q.id].ready
    <2>0. s.cache = [id \in RequestIds |-> s.cache[id]]
          /\ p.id \in RequestIds /\ q.id \in RequestIds /\ p.id # q.id
        BY SMT DEF PointStates, ClientCommands
    <2>1. [[s.cache EXCEPT ![p.id] = [ready |-> TRUE, value |-> Reply(s.db, p)]]
                         EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]
        = [[s.cache EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]
                         EXCEPT ![p.id] = [ready |-> TRUE, value |-> Reply(s.db, p)]]
        BY ONLY DistinctFunctionUpdatesCommute, <2>0
    <2>10. PointTransition(s, p) =
               [db |-> Effect(s.db, p),
                cache |-> [s.cache EXCEPT ![p.id] = [ready |-> TRUE, value |-> Reply(s.db, p)]]]
           /\ PointTransition(s, q) =
               [db |-> Effect(s.db, q),
                cache |-> [s.cache EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]]
        BY ONLY <1>5 DEF PointTransition
    <2>2. PointTransition(PointTransition(s, p), q) =
             [db |-> Effect(Effect(s.db, p), q),
              cache |-> [[s.cache EXCEPT ![p.id] = [ready |-> TRUE, value |-> Reply(s.db, p)]]
                             EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]]
        BY ONLY <1>1, <1>2, <1>5, <2>10, Isa DEF PointTransition
    <2>3. PointTransition(PointTransition(s, q), p) =
             [db |-> Effect(Effect(s.db, q), p),
              cache |-> [[s.cache EXCEPT ![q.id] = [ready |-> TRUE, value |-> Reply(s.db, q)]]
                             EXCEPT ![p.id] = [ready |-> TRUE, value |-> Reply(s.db, p)]]]
        BY ONLY <1>1, <1>2, <1>5, <2>10, Isa DEF PointTransition
    <2> QED BY ONLY <1>2, <2>1, <2>2, <2>3
<1> QED BY <1>3, <1>4, <1>5

THEOREM ActualApplicationIsPointTransition ==
    ASSUME NEW r \in Replicas, NEW e, e.kind = "data", e.value \in ClientCommands,
           machine \in [Replicas -> [Keys -> Values \cup {Missing}]],
           cache \in [Replicas -> [RequestIds -> [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]],
           ApplyClient(r, e)
    PROVE [db |-> machine'[r], cache |-> cache'[r]]
        = PointTransition([db |-> machine[r], cache |-> cache[r]], e.value)
<1>1. CASE cache[r][e.value.id].ready
    BY SMT, <1>1 DEF ApplyClient, PointTransition
<1>2. CASE ~cache[r][e.value.id].ready
    <2>1. machine'[r] = Effect(machine[r], e.value)
          /\ cache'[r] = [cache[r] EXCEPT ![e.value.id] =
                         [ready |-> TRUE, value |-> Reply(machine[r], e.value)]]
        BY SMT, NestedUpdateAtKnownReplica, <1>2 DEF ApplyClient
    <2> QED BY SMT, <1>2, <2>1 DEF PointTransition
<1> QED BY <1>1, <1>2
=============================================================================
