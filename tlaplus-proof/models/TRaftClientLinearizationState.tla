-------------------- MODULE TRaftClientLinearizationState --------------------
EXTENDS TRaftClientCore, TRaftEntryOrderState, TRaftSequenceFold

\* Shared proof-compatible definitions. TRaftSharedClientSpecification makes
\* these the live observer in both the finite and proof models. TRaftClients
\* retains the old recursive algorithms as independent diagnostic checks.
LinearizationEntryStep(state, e) ==
    IF e.value.id \in Ids(state.order) THEN state
    ELSE [order |-> Append(state.order, e.value.id),
          db |-> Effect(state.db, e.value),
          answers |-> [state.answers EXCEPT ![e.value.id] = Reply(state.db, e.value)]]
SortedIncorporation(entries, order, db, answers) ==
    Fold(SortedEntryOrder(entries), [order |-> order, db |-> db, answers |-> answers],
         LinearizationEntryStep)

ProofObserveLinearization ==
    LET entries == {f.entry : f \in commitHistory'}
        added == {e \in entries : e.kind = "data" /\ e.value.id \notin Ids(witness)}
        result == SortedIncorporation(added, witness, abstractMachine, abstractAnswers)
    IN /\ witness' = result.order /\ abstractMachine' = result.db
       /\ abstractAnswers' = result.answers
ProofClientSpec == ClientSpecification(ProofObserveLinearization)

FiniteOrders(S) == {order \in [1..Cardinality(S) -> S] : Enumerates(order, S)}
SequentialRequestStep(state, id) ==
    [db |-> Effect(state.db, Command(id)),
     answers |-> [state.answers EXCEPT ![id] = Reply(state.db, Command(id))]]
FoldExecuteOrder(order, db, answers) ==
    Fold(order, [db |-> db, answers |-> answers], SequentialRequestStep)
ProofRespectsRealTime(order) ==
    \A i, j \in 1..Len(history) :
      (/\ i < j /\ history[i].kind = "return" /\ history[j].kind = "call"
       /\ history[i].id \in Ids(order) /\ history[j].id \in Ids(order)) =>
          Position(order, history[i].id) < Position(order, history[j].id)
FoldHistoryLinearizable == \E order \in FiniteOrders(CalledIds) :
    /\ ProofRespectsRealTime(order)
    /\ LET result == FoldExecuteOrder(order, EmptyMachine, EmptyAnswers)
       IN \A m \in returned : m.value = result.answers[m.id]
=============================================================================
