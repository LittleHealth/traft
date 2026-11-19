-------------------- MODULE TRaftClientHistoryCompletion ---------------------
EXTENDS TRaftFiniteRequestOrder, TRaftClientWitnessRepresentation

SequentialStates == [db : [Keys -> Values \cup {Missing}],
                     answers : [RequestIds -> Values \cup {Missing, "OK"}]]

THEOREM SequentialCalledRequestIsTyped ==
    ASSUME RequestIdentityState, NEW s \in SequentialStates, NEW id \in CalledIds
    PROVE SequentialRequestStep(s, id) \in SequentialStates
<1>1. PICK q \in calls : q.id = id
    BY DEF CalledIds
<1>2. q \in ClientCommands /\ q.id \in RequestIds /\ Command(id) = q
      /\ s.db \in [Keys -> Values \cup {Missing}]
      /\ s.answers \in [RequestIds -> Values \cup {Missing, "OK"}]
    BY UniqueCallsDetermineCommand, <1>1 DEF RequestIdentityState, ClientCommands, SequentialStates
<1>3. Effect(s.db, q) \in [Keys -> Values \cup {Missing}]
      /\ Reply(s.db, q) \in Values \cup {Missing, "OK"}
    BY TypedPointEffectAndReply, <1>2
<1> QED BY SMT, <1>1, <1>2, <1>3 DEF SequentialRequestStep, SequentialStates

THEOREM CompletingOtherIdentitiesKeepsOldReplies ==
    ASSUME RequestIdentityState, NEW P, P \subseteq RequestIds,
           NEW order \in Seq(CalledIds \ P), NEW initial \in SequentialStates
    PROVE \A id \in P : Fold(order, initial, SequentialRequestStep).answers[id] = initial.answers[id]
<1>0. order \in Seq(CalledIds \ P)
    OBVIOUS
<1>1. DEFINE K(s) == s \in SequentialStates /\ \A id \in P : s.answers[id] = initial.answers[id]
<1>2. K(initial)
    BY DEF K
<1>3. ASSUME NEW s, NEW qid \in CalledIds \ P, K(s)
      PROVE K(SequentialRequestStep(s, qid))
    <2>1. s \in SequentialStates /\ qid \in CalledIds
          /\ \A id \in P : s.answers[id] = initial.answers[id] /\ id # qid
        BY <1>3 DEF K
    <2>2. SequentialRequestStep(s, qid) \in SequentialStates
        BY SequentialCalledRequestIsTyped, <2>1
    <2>3. \A id \in P : SequentialRequestStep(s, qid).answers[id] = s.answers[id]
        BY SMT, <2>1 DEF SequentialRequestStep, SequentialStates
    <2> QED BY <2>1, <2>2, <2>3 DEF K
<1> HIDE DEF K
<1>4. K(Fold(order, initial, SequentialRequestStep))
    BY ONLY FoldPreservesStatePredicate, <1>0, <1>2, <1>3, IsaM("blast")
<1> QED BY <1>4 DEF K

THEOREM DisjointEnumerationsConcatenate ==
    ASSUME NEW S, NEW T, S \cap T = {}, NEW a, Enumerates(a, S), NEW b, Enumerates(b, T)
    PROVE Enumerates(a \o b, S \cup T)
<1>1. a \in Seq(S \cup T) /\ b \in Seq(S \cup T)
      /\ a \in Seq(S) /\ b \in Seq(T)
    BY SeqMonotonic DEF Enumerates
<1>2. a \o b \in Seq(S \cup T)
      /\ Range(a) = SequenceEntries(a) /\ Range(b) = SequenceEntries(b)
      /\ Range(a \o b) = SequenceEntries(a \o b)
      /\ Range(a \o b) = Range(a) \cup Range(b)
      /\ DOMAIN a = 1..Len(a) /\ DOMAIN b = 1..Len(b)
      /\ DOMAIN (a \o b) = 1..Len(a \o b)
    <2>1. a \o b \in Seq(S \cup T)
        BY ONLY ConcatProperties, <1>1
    <2>2. Range(a) = SequenceEntries(a)
        BY ONLY RangeEquality, <1>1 DEF SequenceEntries
    <2>3. Range(b) = SequenceEntries(b)
        BY ONLY RangeEquality, <1>1 DEF SequenceEntries
    <2>4. Range(a \o b) = SequenceEntries(a \o b)
        BY ONLY RangeEquality, <2>1 DEF SequenceEntries
    <2>5. Range(a \o b) = Range(a) \cup Range(b)
        BY ONLY RangeConcatenation, <1>1
    <2>6. DOMAIN a = 1..Len(a) /\ DOMAIN b = 1..Len(b)
          /\ DOMAIN (a \o b) = 1..Len(a \o b)
        BY ONLY LenProperties, <1>1, <2>1
    <2> QED BY ONLY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>3. IsInjective(a) /\ IsInjective(b) /\ Range(a) \cap Range(b) = {}
    BY <1>2 DEF Enumerates, IsInjective
<1>4. IsInjective(a \o b)
    BY ConcatInjectiveSeq, <1>1, <1>3
<1> QED BY <1>2, <1>4 DEF Enumerates, IsInjective

THEOREM ConcatenationExtendsOrderPrefix ==
    ASSUME NEW a \in Seq(RequestIds), NEW b \in Seq(RequestIds)
    PROVE OrderPrefix(a, a \o b)
<1>1. Len(a) \in Nat /\ Len(b) \in Nat
      /\ Len(a \o b) = Len(a) + Len(b)
      /\ \A i \in 1..(Len(a) + Len(b)) :
          (a \o b)[i] = IF i <= Len(a) THEN a[i] ELSE b[i - Len(a)]
    BY LenProperties, ConcatProperties
<1> QED BY SMT, <1>1 DEF OrderPrefix

\* Pending requests may be completed after the witness. Their effects cannot
\* overwrite already-returned identities because each identity occurs once.
THEOREM SequentialWitnessImpliesIndependentHistory ==
    ASSUME RequestIdentityState, RequestHistoryState, IsFiniteSet(CalledIds),
           WitnessRepresentation, Ids(witness) \subseteq CalledIds,
           RealTimeIn(history, witness), ReturnedIds \subseteq Ids(witness),
           \A m \in returned : m.value = abstractAnswers[m.id]
    PROVE FoldHistoryLinearizable
<1>1. DEFINE pendingIds == CalledIds \ Ids(witness)
<1>2. IsFiniteSet(pendingIds) /\ pendingIds \subseteq RequestIds /\ CalledIds \subseteq RequestIds
    BY FS_Subset DEF pendingIds, CalledIds, RequestIdentityState, ClientCommands
<1>3. PICK suffix \in FiniteOrders(pendingIds) : TRUE
    BY FiniteSetHasAnEnumeratingOrder, <1>2
<1>4. Enumerates(suffix, pendingIds) /\ suffix \in Seq(RequestIds)
      /\ witness \in Seq(RequestIds) /\ UniqueOrder(witness)
    BY SeqMonotonic, <1>2, <1>3
       DEF FiniteOrders, Enumerates, WitnessRepresentation, WitnessStateNow, WitnessStates
<1>5. witness \in Seq(Ids(witness))
    BY SequenceUsesItsElementAlphabet, <1>4
<1>6. Enumerates(witness, Ids(witness)) /\ Ids(witness) \cap pendingIds = {}
      /\ Ids(witness) \cup pendingIds = CalledIds
    BY <1>4, <1>5 DEF Enumerates, UniqueOrder, SequenceEntries, Ids, pendingIds
<1>7. DEFINE completed == witness \o suffix
<1>8. Enumerates(completed, CalledIds) /\ completed \in Seq(RequestIds)
      /\ OrderPrefix(witness, completed) /\ UniqueOrder(completed)
    <2>1. Enumerates(completed, Ids(witness) \cup pendingIds)
        BY ONLY DisjointEnumerationsConcatenate, <1>4, <1>6 DEF completed
    <2>2. Enumerates(completed, CalledIds)
        BY ONLY <2>1, <1>6
    <2>3. completed \in Seq(RequestIds)
        BY ONLY ConcatProperties, <1>4 DEF completed
    <2>4. OrderPrefix(witness, completed)
        BY ONLY ConcatenationExtendsOrderPrefix, <1>4 DEF completed
    <2>5. UniqueOrder(completed)
        BY ONLY <2>2 DEF Enumerates, UniqueOrder
    <2> QED BY ONLY <2>2, <2>3, <2>4, <2>5
<1>9. completed \in FiniteOrders(CalledIds)
    BY EnumeratingOrderHasCardinalLength, <1>8
<1>10. history \in Seq(ClientEvents)
       /\ \A i \in 1..Len(history) : history[i].kind = "return" => history[i].id \in Ids(witness)
    BY DEF RequestHistoryState, HistoryReturnSources, ReturnedIds
<1>11. RealTimeIn(history, completed) /\ ProofRespectsRealTime(completed)
    BY ExtendingWitnessPreservesRecordedRealTime, <1>4, <1>8, <1>10
       DEF ProofRespectsRealTime, RealTimeIn
<1>12. DEFINE initial == [db |-> abstractMachine, answers |-> abstractAnswers]
<1>13. initial \in SequentialStates /\ Ids(witness) \subseteq RequestIds
       /\ Fold(witness, [db |-> EmptyMachine, answers |-> EmptyAnswers], SequentialRequestStep) = initial
    BY LenProperties, <1>4
       DEF initial, WitnessRepresentation, WitnessSequential, WitnessStateNow, WitnessStates,
           SequentialStates, FoldExecuteOrder, Ids
<1>14. \A id \in Ids(witness) :
           Fold(suffix, initial, SequentialRequestStep).answers[id] = abstractAnswers[id]
    BY CompletingOtherIdentitiesKeepsOldReplies, <1>3, <1>13
       DEF FiniteOrders, Enumerates, pendingIds, initial
<1>15. FoldExecuteOrder(completed, EmptyMachine, EmptyAnswers)
          = Fold(suffix, initial, SequentialRequestStep)
    BY FoldConcatenation, <1>4, <1>13 DEF completed, FoldExecuteOrder
<1>16. \A m \in returned :
           m.value = FoldExecuteOrder(completed, EmptyMachine, EmptyAnswers).answers[m.id]
    BY <1>14, <1>15 DEF ReturnedIds
<1> QED BY <1>9, <1>11, <1>16 DEF FoldHistoryLinearizable
=============================================================================
