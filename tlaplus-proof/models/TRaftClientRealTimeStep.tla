----------------------- MODULE TRaftClientRealTimeStep -----------------------
EXTENDS TRaftClientOrderProof, TRaftClientHistoryFacts

EvidenceRequestIds == {e.value.id : e \in {x \in EvidenceEntries : x.kind = "data"}}

THEOREM AppendingReturnKeepsRealTime ==
    ASSUME NEW E, NEW events \in Seq(E), NEW event \in E, event.kind = "return",
           NEW order, RealTimeIn(events, order)
    PROVE RealTimeIn(Append(events, event), order)
<1>1. Len(events) \in Nat /\ Len(Append(events, event)) = Len(events) + 1
      /\ (\A i \in 1..Len(events) : Append(events, event)[i] = events[i])
      /\ Append(events, event)[Len(events) + 1] = event
    BY LenProperties, AppendProperties
<1> QED BY SMT, <1>1 DEF RealTimeIn

THEOREM AppendingUnlinearizedCallKeepsRealTime ==
    ASSUME NEW E, NEW events \in Seq(E), NEW event \in E,
           NEW order, event.id \notin Ids(order), RealTimeIn(events, order)
    PROVE RealTimeIn(Append(events, event), order)
<1>1. Len(events) \in Nat /\ Len(Append(events, event)) = Len(events) + 1
      /\ (\A i \in 1..Len(events) : Append(events, event)[i] = events[i])
      /\ Append(events, event)[Len(events) + 1] = event
    BY LenProperties, AppendProperties
<1> QED BY SMT, <1>1 DEF RealTimeIn

THEOREM InvokedIdentityIsFresh ==
    ASSUME RequestIdentityState, NEW q \in ClientCommands, Invoke(q)
    PROVE q.id \notin CalledIds
<1>1. q.id[1] \in Clients /\ q.id[2] = nextSequence[q.id[1]]
      /\ q.id[2] \in Nat
    BY DEF Invoke, ClientCommands, RequestIds, SeqDomain
<1> QED BY SMT, <1>1 DEF RequestIdentityState, CalledIds

THEOREM StutteringAcksKeepEvidenceEntries ==
    ASSUME CommitEvidenceSound, Observe, UNCHANGED ackMessages
    PROVE UNCHANGED EvidenceEntries
<1>1. commitHistory' = commitHistory
    BY DEF CommitEvidenceSound, Observe
<1> QED BY <1>1 DEF EvidenceEntries

THEOREM EvidenceIdentitiesHaveCalls ==
    ASSUME \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
    PROVE EvidenceRequestIds \subseteq CalledIds
BY DEF EvidenceRequestIds, CalledIds

\* The post-state identity set is supplied by a separate observer induction.
\* No post-state real-time property is assumed here.
THEOREM ClientEventsPreserveRealTime ==
    ASSUME RequestHistoryState, RequestIdentityState, ReplySources, ApplicationTypes,
           CommitEvidenceSound, Observe, ClientAction,
           witness \in Seq(RequestIds), witness' \in Seq(RequestIds),
           OrderPrefix(witness, witness'), UniqueOrder(witness'),
           RealTimeIn(history, witness), ReturnedIds \subseteq Ids(witness),
           Ids(witness') = EvidenceRequestIds',
           \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
    PROVE RealTimeIn(history', witness')
<1>1. history \in Seq(ClientEvents)
      /\ \A i \in 1..Len(history) : history[i].kind = "return" => history[i].id \in Ids(witness)
    BY DEF RequestHistoryState, HistoryReturnSources, ReturnedIds
<1>2. RealTimeIn(history, witness')
    BY ExtendingWitnessPreservesRecordedRealTime, <1>1
<1>3. (\E q \in ClientCommands : Invoke(q)) \/ (\E m \in replyMessages : ReceiveReply(m))
          \/ UNCHANGED <<calls, history, returned>>
    BY OnlyInvocationOrReceiptChangesHistory
<1>4. CASE \E q \in ClientCommands : Invoke(q)
    <2>1. PICK q \in ClientCommands : Invoke(q)
        BY <1>4
    <2>2. UNCHANGED ackMessages /\ q.id \notin CalledIds
          /\ [kind |-> "call", id |-> q.id, value |-> Missing] \in ClientEvents
        BY InvokedIdentityIsFresh, <2>1 DEF Invoke, protocolVars, ClientCommands, ClientEvents
    <2>3. UNCHANGED EvidenceEntries /\ EvidenceRequestIds \subseteq CalledIds
        BY StutteringAcksKeepEvidenceEntries, EvidenceIdentitiesHaveCalls, <2>2
    <2>4. q.id \notin Ids(witness')
        BY <2>2, <2>3 DEF EvidenceRequestIds
    <2> QED BY AppendingUnlinearizedCallKeepsRealTime, <1>1, <1>2, <2>1, <2>2, <2>4 DEF Invoke
<1>5. CASE \E m \in replyMessages : ReceiveReply(m)
    <2>1. PICK m \in replyMessages : ReceiveReply(m)
        BY <1>5
    <2>2. m.id \in RequestIds /\ m.value \in Values \cup {Missing, "OK"}
        BY DurableReplySourcesAreTyped, <2>1
    <2>3. [kind |-> "return", id |-> m.id, value |-> m.value] \in ClientEvents
        BY <2>2 DEF ClientEvents
    <2> QED BY AppendingReturnKeepsRealTime, <1>1, <1>2, <2>1, <2>3 DEF ReceiveReply
<1>6. CASE UNCHANGED <<calls, history, returned>>
    BY <1>2, <1>6
<1> QED BY <1>3, <1>4, <1>5, <1>6
=============================================================================
