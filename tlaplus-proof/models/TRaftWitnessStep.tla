-------------------------- MODULE TRaftWitnessStep ---------------------------
EXTENDS TRaftClientOrderProof, TRaftDeduplicatedCommutation,
        TRaftPointStoreEvaluation, TRaftFoldSimulation

WitnessStates == [order : Seq(RequestIds), db : [Keys -> Values \cup {Missing}],
                  answers : [RequestIds -> Values \cup {Missing, "OK"}]]
WitnessCache(s) == [id \in RequestIds |->
    [ready |-> id \in Ids(s.order), value |-> s.answers[id]]]
WitnessPoint(s) == [db |-> s.db, cache |-> WitnessCache(s)]
WitnessSequential(s) == FoldExecuteOrder(s.order, EmptyMachine, EmptyAnswers)
                          = [db |-> s.db, answers |-> s.answers]

THEOREM AppendHasExactlyOneMoreIdentity ==
    ASSUME NEW order \in Seq(RequestIds), NEW id \in RequestIds
    PROVE Ids(Append(order, id)) = Ids(order) \cup {id}
<1>1. Len(order) \in Nat /\ Len(Append(order, id)) = Len(order) + 1
      /\ (\A i \in 1..Len(order) : Append(order, id)[i] = order[i])
      /\ Append(order, id)[Len(order) + 1] = id
    BY LenProperties, AppendProperties
<1> QED BY SMT, <1>1 DEF Ids

THEOREM AppendFreshIdentityKeepsUniquePrefix ==
    ASSUME NEW order \in Seq(RequestIds), UniqueOrder(order),
           NEW id \in RequestIds, id \notin Ids(order)
    PROVE Append(order, id) \in Seq(RequestIds)
          /\ UniqueOrder(Append(order, id)) /\ OrderPrefix(order, Append(order, id))
<1>1. Len(order) \in Nat /\ Append(order, id) \in Seq(RequestIds)
      /\ Len(Append(order, id)) = Len(order) + 1
      /\ (\A i \in 1..Len(order) : Append(order, id)[i] = order[i])
      /\ Append(order, id)[Len(order) + 1] = id
    BY LenProperties, AppendProperties
<1> QED BY SMT, <1>1 DEF UniqueOrder, OrderPrefix, Ids

THEOREM TypedPointEffectAndReply ==
    ASSUME NEW db \in [Keys -> Values \cup {Missing}], NEW q \in ClientCommands
    PROVE Effect(db, q) \in [Keys -> Values \cup {Missing}]
          /\ Reply(db, q) \in Values \cup {Missing, "OK"}
BY SMT DEF ClientCommands, Effect, Reply

THEOREM LinearizationStepHasTypedUniqueOrder ==
    ASSUME NEW s \in WitnessStates, UniqueOrder(s.order),
           NEW e, e.value \in ClientCommands
    PROVE LinearizationEntryStep(s, e) \in WitnessStates
          /\ UniqueOrder(LinearizationEntryStep(s, e).order)
          /\ OrderPrefix(s.order, LinearizationEntryStep(s, e).order)
          /\ Ids(LinearizationEntryStep(s, e).order) = Ids(s.order) \cup {e.value.id}
<1>1. s.order \in Seq(RequestIds) /\ s.db \in [Keys -> Values \cup {Missing}]
      /\ s.answers \in [RequestIds -> Values \cup {Missing, "OK"}]
      /\ e.value.id \in RequestIds /\ Len(s.order) \in Nat
    BY LenProperties DEF WitnessStates, ClientCommands
<1>2. Effect(s.db, e.value) \in [Keys -> Values \cup {Missing}]
      /\ Reply(s.db, e.value) \in Values \cup {Missing, "OK"}
    BY TypedPointEffectAndReply, <1>1
<1>3. CASE e.value.id \in Ids(s.order)
    BY SMT, <1>1, <1>3 DEF LinearizationEntryStep, OrderPrefix
<1>4. CASE e.value.id \notin Ids(s.order)
    <2>1. Append(s.order, e.value.id) \in Seq(RequestIds)
          /\ UniqueOrder(Append(s.order, e.value.id))
          /\ OrderPrefix(s.order, Append(s.order, e.value.id))
          /\ Ids(Append(s.order, e.value.id)) = Ids(s.order) \cup {e.value.id}
        BY AppendFreshIdentityKeepsUniquePrefix, AppendHasExactlyOneMoreIdentity, <1>1, <1>4
    <2>2. [s.answers EXCEPT ![e.value.id] = Reply(s.db, e.value)]
            \in [RequestIds -> Values \cup {Missing, "OK"}]
        BY ONLY SMT, <1>1, <1>2
    <2> QED BY <1>1, <1>2, <1>4, <2>1, <2>2 DEF LinearizationEntryStep, WitnessStates
<1> QED BY <1>3, <1>4

THEOREM WitnessCacheIsTyped ==
    ASSUME NEW s \in WitnessStates
    PROVE WitnessPoint(s) \in PointStates
BY SMT DEF WitnessStates, WitnessPoint, WitnessCache, PointStates

THEOREM LinearizationStepSimulatesDeduplicatedPointStep ==
    ASSUME NEW s \in WitnessStates, NEW e, e.value \in ClientCommands
    PROVE WitnessPoint(LinearizationEntryStep(s, e)) = PointTransition(WitnessPoint(s), e.value)
<1>1. e.value.id \in RequestIds /\ s.order \in Seq(RequestIds)
      /\ s.answers \in [RequestIds -> Values \cup {Missing, "OK"}]
    BY DEF WitnessStates, ClientCommands
<1>2. CASE e.value.id \in Ids(s.order)
    <2>1. LinearizationEntryStep(s, e) = s
        BY ONLY <1>2 DEF LinearizationEntryStep
    <2>2. WitnessCache(s)[e.value.id].ready
        <3>1. WitnessCache(s)[e.value.id] =
                  [ready |-> e.value.id \in Ids(s.order), value |-> s.answers[e.value.id]]
            BY ONLY SMT, <1>1 DEF WitnessCache
        <3> QED BY ONLY IsaM("auto"), <1>2, <3>1
    <2>3. WitnessPoint(s).cache[e.value.id].ready
        BY ONLY <2>2 DEF WitnessPoint
    <2>4. PointTransition(WitnessPoint(s), e.value) = WitnessPoint(s)
        BY ONLY <2>3 DEF PointTransition
    <2> QED BY ONLY <2>1, <2>4
<1>3. CASE e.value.id \notin Ids(s.order)
    <2>1. Ids(Append(s.order, e.value.id)) = Ids(s.order) \cup {e.value.id}
        BY AppendHasExactlyOneMoreIdentity, <1>1
    <2>2. DEFINE next == LinearizationEntryStep(s, e)
                updated == [WitnessCache(s) EXCEPT ![e.value.id] =
                               [ready |-> TRUE, value |-> Reply(s.db, e.value)]]
    <2>20. next.order = Append(s.order, e.value.id)
           /\ next.answers = [s.answers EXCEPT ![e.value.id] = Reply(s.db, e.value)]
        BY ONLY <1>3 DEF next, LinearizationEntryStep
    <2>21. Ids(next.order) = Ids(s.order) \cup {e.value.id}
        BY ONLY <2>1, <2>20
    <2>3. WitnessCache(next) = [id \in RequestIds |-> WitnessCache(next)[id]]
          /\ WitnessCache(s) = [id \in RequestIds |-> WitnessCache(s)[id]]
        BY Isa DEF WitnessCache
    <2>4. updated = [id \in RequestIds |-> updated[id]]
        BY FunctionUpdatePreservesDomainShape, <1>1, <2>3 DEF updated
    <2>5. \A id \in RequestIds : WitnessCache(next)[id] = updated[id]
        <3>1. ASSUME NEW id \in RequestIds
              PROVE WitnessCache(next)[id] = updated[id]
            <4>1. WitnessCache(next)[id] =
                      [ready |-> id \in Ids(next.order), value |-> next.answers[id]]
                  /\ WitnessCache(s)[id] =
                      [ready |-> id \in Ids(s.order), value |-> s.answers[id]]
                BY ONLY SMT, <3>1 DEF WitnessCache
            <4>2. updated[id] = IF id = e.value.id
                      THEN [ready |-> TRUE, value |-> Reply(s.db, e.value)]
                      ELSE WitnessCache(s)[id]
                BY ONLY SMT, <1>1, <2>3, <3>1 DEF updated
            <4>3. next.answers[id] = IF id = e.value.id
                      THEN Reply(s.db, e.value) ELSE s.answers[id]
                BY ONLY SMT, <1>1, <2>20, <3>1
            <4>4. (id \in Ids(next.order)) <=> (id \in Ids(s.order) \/ id = e.value.id)
                BY ONLY <2>21
            <4>5. CASE id = e.value.id
                <5>1. id \notin Ids(s.order) /\ id \in Ids(next.order)
                    BY ONLY <1>3, <4>4, <4>5
                <5> QED BY ONLY IsaM("auto"), <4>1, <4>2, <4>3, <4>5, <5>1
            <4>6. CASE id # e.value.id
                BY ONLY IsaM("auto"), <4>1, <4>2, <4>3, <4>4, <4>6
            <4> QED BY ONLY <4>5, <4>6
        <3> QED BY ONLY <3>1
    <2>6. WitnessCache(next) = updated
        BY EqualFunctionValuesDetermineFunction, <2>3, <2>4, <2>5
    <2>7. ~WitnessCache(s)[e.value.id].ready
        BY <1>1, <1>3 DEF WitnessCache
    <2> QED BY <1>3, <2>6, <2>7
        DEF next, updated, LinearizationEntryStep, WitnessPoint, PointTransition
<1> QED BY <1>2, <1>3

THEOREM UniqueCallsDetermineCommand ==
    ASSUME RequestIdentityState, NEW q \in calls
    PROVE Command(q.id) = q
BY ZenonT(5) DEF RequestIdentityState, Command

THEOREM LinearizationStepKeepsSequentialExecution ==
    ASSUME RequestIdentityState, NEW s \in WitnessStates, WitnessSequential(s),
           NEW e, e.value \in calls
    PROVE WitnessSequential(LinearizationEntryStep(s, e))
<1>1. s.order \in Seq(RequestIds) /\ e.value.id \in RequestIds
      /\ Command(e.value.id) = e.value
    BY UniqueCallsDetermineCommand DEF WitnessStates, RequestIdentityState, ClientCommands
<1>2. CASE e.value.id \in Ids(s.order)
    BY <1>2 DEF LinearizationEntryStep
<1>3. CASE e.value.id \notin Ids(s.order)
    <2>1. Fold(Append(s.order, e.value.id), [db |-> EmptyMachine, answers |-> EmptyAnswers],
                SequentialRequestStep)
           = SequentialRequestStep(
                Fold(s.order, [db |-> EmptyMachine, answers |-> EmptyAnswers], SequentialRequestStep),
                e.value.id)
        BY FoldAppend, <1>1
    <2> QED BY <1>1, <1>3, <2>1
        DEF WitnessSequential, FoldExecuteOrder, LinearizationEntryStep, SequentialRequestStep
<1> QED BY <1>2, <1>3
=============================================================================
