---------------------------- MODULE TRaftClients -----------------------------
EXTENDS TRaftSharedClientSpecification

\* This witness is derived from ACK evidence, independently of replies and
\* application. It never enables or disables ClientAction.
RECURSIVE Incorporate(_, _, _, _)
Incorporate(entries, order, db, answers) ==
    IF entries = {} THEN [order |-> order, db |-> db, answers |-> answers]
    ELSE LET e == CHOOSE x \in entries : \A y \in entries : x.index <= y.index
             q == e.value
         IN IF q.id \in Ids(order) THEN Incorporate(entries \ {e}, order, db, answers)
            ELSE Incorporate(entries \ {e}, Append(order, q.id), Effect(db, q),
                             [answers EXCEPT ![q.id] = Reply(db, q)])

\* Historical recursive observer retained for differential checks. The live
\* observer and ClientSpec are inherited from the shared specification.
RecursiveObserveLinearization ==
    LET entries == {f.entry : f \in commitHistory'}
        added == {e \in entries : e.kind = "data" /\ e.value.id \notin Ids(witness)}
        result == Incorporate(added, witness, abstractMachine, abstractAnswers)
    IN /\ witness' = result.order /\ abstractMachine' = result.db
       /\ abstractAnswers' = result.answers

RECURSIVE Orders(_)
Orders(S) == IF S = {} THEN {<<>>}
             ELSE (UNION {{Append(prefix, id) : prefix \in Orders(S \ {id})} : id \in S})
RECURSIVE ExecuteOrder(_, _, _)
ExecuteOrder(order, db, answers) ==
    IF order = <<>> THEN [db |-> db, answers |-> answers]
    ELSE LET q == Command(Head(order))
         IN ExecuteOrder(Tail(order), Effect(db, q), [answers EXCEPT ![q.id] = Reply(db, q)])
RespectsRealTime(order) ==
    \A i, j \in 1..Len(history) :
      (/\ i < j /\ history[i].kind = "return" /\ history[j].kind = "call"
       /\ history[i].id \in Ids(order) /\ history[j].id \in Ids(order)) =>
          Position(order, history[i].id) < Position(order, history[j].id)

\* Independent finite-history definition: tries all sequential explanations,
\* without consulting ACKs, local commitment, applied IDs, or the witness.
\* Pending calls may be completed at the end of the history.
HistoryLinearizable == \E order \in Orders(CalledIds) :
    /\ RespectsRealTime(order)
    /\ LET result == ExecuteOrder(order, EmptyMachine, EmptyAnswers)
       IN \A m \in returned : m.value = result.answers[m.id]

WitnessValid ==
    /\ Ids(witness) \subseteq CalledIds /\ ReturnedIds \subseteq Ids(witness)
    /\ \A i, j \in 1..Len(witness) : witness[i] = witness[j] => i = j
    /\ RespectsRealTime(witness)
    /\ \A m \in returned : m.value = abstractAnswers[m.id]
    /\ ExecuteOrder(witness, EmptyMachine, EmptyAnswers) =
          [db |-> abstractMachine, answers |-> abstractAnswers]

ClientSafety == /\ Safety /\ ClientTypeOK /\ ReadIsolation
                /\ PartitionCommandsIndependent /\ CacheHasAppliedRequest
                /\ WitnessValid /\ HistoryLinearizable
=============================================================================
