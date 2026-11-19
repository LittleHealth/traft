--------------------- MODULE TRaftClientCommandStability ---------------------
EXTENDS TRaftClientLinearizationState, TRaftClientPersistenceProof, TRaftFoldSimulation

CommandFrom(Q, id) == CHOOSE q \in Q : q.id = id
RequestStepFrom(Q, s, id) ==
    [db |-> Effect(s.db, CommandFrom(Q, id)),
     answers |-> [s.answers EXCEPT ![id] = Reply(s.db, CommandFrom(Q, id))]]
ExecutionFrom(Q, order, db, answers) ==
    Fold(order, [db |-> db, answers |-> answers], LAMBDA s, id : RequestStepFrom(Q, s, id))

THEOREM EqualStepFunctionsHaveEqualFolds ==
    ASSUME NEW S, NEW order \in Seq(S), NEW initial, NEW F(_, _), NEW G(_, _),
           \A s : \A e \in S : F(s, e) = G(s, e)
    PROVE Fold(order, initial, F) = Fold(order, initial, G)
<1>1. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>2. DEFINE P(n) == n <= Len(order) =>
          FoldTrace(order, initial, F)[n] = FoldTrace(order, initial, G)[n]
<1>3. P(0)
    BY FoldTraceStartsAtInitial DEF P
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE P(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE FoldTrace(order, initial, F)[n + 1]
                          = FoldTrace(order, initial, G)[n + 1]
        BY DEF P
    <2>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
          /\ order[n + 1] \in S /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. FoldTrace(order, initial, F)[n] = FoldTrace(order, initial, G)[n]
        BY <1>4, <2>2 DEF P
    <2>4. FoldTrace(order, initial, F)[n + 1]
              = F(FoldTrace(order, initial, F)[n], order[n + 1])
          /\ FoldTrace(order, initial, G)[n + 1]
              = G(FoldTrace(order, initial, G)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>5. \A n \in Nat : P(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF P, Fold

THEOREM UniqueRequestDeterminesParameterizedCommand ==
    ASSUME NEW Q, \A p, q \in Q : p.id = q.id => p = q, NEW q \in Q
    PROVE CommandFrom(Q, q.id) = q
BY ZenonT(5) DEF CommandFrom

THEOREM ExtendingCallsKeepsExistingCommands ==
    ASSUME NEW Q, NEW R, Q \subseteq R, \A p, q \in R : p.id = q.id => p = q,
           NEW id \in {q.id : q \in Q}
    PROVE CommandFrom(Q, id) = CommandFrom(R, id)
<1>1. PICK q \in Q : q.id = id
    OBVIOUS
<1>2. q \in R /\ \A p, t \in Q : p.id = t.id => p = t
    BY <1>1
<1>3. CommandFrom(Q, q.id) = q /\ CommandFrom(R, q.id) = q
    BY UniqueRequestDeterminesParameterizedCommand, <1>1, <1>2
<1> QED BY <1>1, <1>3

THEOREM ExtendingCallsKeepsExistingExecutions ==
    ASSUME NEW Q, NEW R, Q \subseteq R, \A p, q \in R : p.id = q.id => p = q,
           NEW order \in Seq({q.id : q \in Q}), NEW db, NEW answers
    PROVE ExecutionFrom(Q, order, db, answers) = ExecutionFrom(R, order, db, answers)
<1>0. order \in Seq({q.id : q \in Q})
    OBVIOUS
<1>1. DEFINE F(s, id) == RequestStepFrom(Q, s, id)
            G(s, id) == RequestStepFrom(R, s, id)
<1>2. \A id \in {q.id : q \in Q} : CommandFrom(Q, id) = CommandFrom(R, id)
    BY ExtendingCallsKeepsExistingCommands
<1>3. \A s : \A id \in {q.id : q \in Q} : F(s, id) = G(s, id)
    BY <1>2 DEF F, G, RequestStepFrom
<1> HIDE DEF F, G
<1>4. Fold(order, [db |-> db, answers |-> answers], F)
          = Fold(order, [db |-> db, answers |-> answers], G)
    BY ONLY EqualStepFunctionsHaveEqualFolds, <1>0, <1>3, IsaM("blast")
<1> QED BY <1>4 DEF F, G, ExecutionFrom

THEOREM CurrentExecutionIdentity ==
    \A order \in Seq(RequestIds) : \A db, answers :
      FoldExecuteOrder(order, db, answers) = ExecutionFrom(calls, order, db, answers)
<1>1. ASSUME NEW order \in Seq(RequestIds), NEW db, NEW answers
      PROVE FoldExecuteOrder(order, db, answers) = ExecutionFrom(calls, order, db, answers)
    <2>0. order \in Seq(RequestIds)
        OBVIOUS
    <2>1. DEFINE G(s, id) == RequestStepFrom(calls, s, id)
    <2>2. \A s : \A id \in RequestIds : SequentialRequestStep(s, id) = G(s, id)
        BY DEF G, RequestStepFrom, SequentialRequestStep, CommandFrom, Command
    <2> HIDE DEF G
    <2>3. Fold(order, [db |-> db, answers |-> answers], SequentialRequestStep)
              = Fold(order, [db |-> db, answers |-> answers], G)
        BY ONLY EqualStepFunctionsHaveEqualFolds, <2>0, <2>2, IsaM("blast")
    <2> QED BY <2>3 DEF G, FoldExecuteOrder, ExecutionFrom
<1> QED BY <1>1

THEOREM ClientCallExtensionKeepsOldExecution ==
    ASSUME RequestIdentityState', calls \subseteq calls',
           NEW order \in Seq(CalledIds), NEW db, NEW answers
    PROVE ExecutionFrom(calls, order, db, answers) = ExecutionFrom(calls', order, db, answers)
<1>1. \A p, q \in calls' : p.id = q.id => p = q
    BY DEF RequestIdentityState
<1> QED BY ExtendingCallsKeepsExistingExecutions, <1>1 DEF CalledIds
=============================================================================
