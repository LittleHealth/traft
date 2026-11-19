----------------------- MODULE TRaftClientHistoryFacts -----------------------
EXTENDS TRaftClientReplySources, TRaftClientApplicationProof, SequenceTheorems,
        FiniteSetTheorems

ClientEvents == [kind : {"call", "return"}, id : RequestIds,
                 value : Values \cup {Missing, "OK"}]
HistoryCallSources == \A i \in 1..Len(history) :
    history[i].kind = "call" => history[i].id \in CalledIds
HistoryReturnSources == \A i \in 1..Len(history) : history[i].kind = "return" =>
    \E m \in returned : m.id = history[i].id /\ m.value = history[i].value
RequestHistoryState ==
    /\ IsFiniteSet(calls) /\ history \in Seq(ClientEvents)
    /\ HistoryCallSources /\ HistoryReturnSources

THEOREM DurableReplySourcesAreTyped ==
    (ReplySources /\ RequestIdentityState /\ ApplicationTypes) =>
      \A m \in replyMessages : m.sender \in Replicas /\ m.id \in RequestIds
                               /\ m.value \in Values \cup {Missing, "OK"}
<1>1. ASSUME ReplySources, RequestIdentityState, ApplicationTypes, NEW m \in replyMessages
      PROVE m.sender \in Replicas /\ m.id \in RequestIds
            /\ m.value \in Values \cup {Missing, "OK"}
    <2>1. PICK q \in calls : q.id = m.id /\ m.sender \in Replicas
              /\ cache[m.sender][m.id].ready /\ m.value = cache[m.sender][m.id].value
        BY <1>1 DEF ReplySources, ReplyHasDurableSource
    <2>2. m.id \in RequestIds /\ m.value \in Values \cup {Missing, "OK"}
        BY <1>1, <2>1 DEF RequestIdentityState, ClientCommands, ApplicationTypes
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1

THEOREM OnlyInvocationOrReceiptChangesHistory == ClientAction =>
    (\E q \in ClientCommands : Invoke(q)) \/ (\E m \in replyMessages : ReceiveReply(m))
      \/ UNCHANGED <<calls, history, returned>>
BY DEF ClientAction, Background, Admit, ClosePartition, ApplyClient, SendReply,
       ReadWithoutBarrier, localClientVars

THEOREM InvokingKeepsHistorySources ==
    ASSUME RequestHistoryState, RequestIdentityState, NEW q \in ClientCommands, Invoke(q)
    PROVE RequestHistoryState'
<1>1. q.id \in RequestIds
      /\ [kind |-> "call", id |-> q.id, value |-> Missing] \in ClientEvents
    BY DEF ClientCommands, ClientEvents
<1>2. calls' = calls \cup {q} /\ returned' = returned
      /\ history' = Append(history, [kind |-> "call", id |-> q.id, value |-> Missing])
      /\ history \in Seq(ClientEvents) /\ IsFiniteSet(calls)
    BY DEF Invoke, RequestHistoryState
<1>3. IsFiniteSet(calls') /\ history' \in Seq(ClientEvents)
      /\ Len(history) \in Nat /\ Len(history') = Len(history) + 1
      /\ (\A i \in 1..Len(history) : history'[i] = history[i])
      /\ history'[Len(history) + 1] = [kind |-> "call", id |-> q.id, value |-> Missing]
    BY FS_AddElement, AppendProperties, LenProperties, <1>1, <1>2
<1> QED BY SMT, <1>1, <1>2, <1>3
    DEF RequestHistoryState, HistoryCallSources, HistoryReturnSources, CalledIds

THEOREM ReceivingKeepsHistorySources ==
    ASSUME RequestHistoryState, NEW m \in replyMessages,
           m.id \in RequestIds, m.value \in Values \cup {Missing, "OK"}, ReceiveReply(m)
    PROVE RequestHistoryState'
<1>1. [kind |-> "return", id |-> m.id, value |-> m.value] \in ClientEvents
    BY DEF ClientEvents
<1>2. calls' = calls /\ returned' = returned \cup {m}
      /\ history' = Append(history, [kind |-> "return", id |-> m.id, value |-> m.value])
      /\ history \in Seq(ClientEvents) /\ IsFiniteSet(calls)
    BY DEF ReceiveReply, RequestHistoryState
<1>3. history' \in Seq(ClientEvents) /\ Len(history) \in Nat
      /\ Len(history') = Len(history) + 1
      /\ (\A i \in 1..Len(history) : history'[i] = history[i])
      /\ history'[Len(history) + 1] = [kind |-> "return", id |-> m.id, value |-> m.value]
    BY AppendProperties, LenProperties, <1>1, <1>2
<1> QED BY SMT, <1>1, <1>2, <1>3
    DEF RequestHistoryState, HistoryCallSources, HistoryReturnSources, CalledIds

THEOREM RequestHistoryInitially == ClientInit => RequestHistoryState
BY SMT, EmptySeq, FS_EmptySet DEF ClientInit, RequestHistoryState, HistoryCallSources, HistoryReturnSources

THEOREM RequestHistoryInductiveStep ==
    ASSUME RequestHistoryState, RequestIdentityState, ApplicationTypes, ReplySources, ClientAction
    PROVE RequestHistoryState'
<1>1. (\E q \in ClientCommands : Invoke(q)) \/ (\E m \in replyMessages : ReceiveReply(m))
          \/ UNCHANGED <<calls, history, returned>>
    BY OnlyInvocationOrReceiptChangesHistory
<1>2. \A m \in replyMessages : m.id \in RequestIds /\ m.value \in Values \cup {Missing, "OK"}
    BY DurableReplySourcesAreTyped
<1>3. CASE \E q \in ClientCommands : Invoke(q)
    BY InvokingKeepsHistorySources, <1>3
<1>4. CASE \E m \in replyMessages : ReceiveReply(m)
    BY ReceivingKeepsHistorySources, <1>2, <1>4
<1>5. CASE UNCHANGED <<calls, history, returned>>
    BY <1>5 DEF RequestHistoryState, HistoryCallSources, HistoryReturnSources, CalledIds
<1> QED BY <1>1, <1>3, <1>4, <1>5
=============================================================================
