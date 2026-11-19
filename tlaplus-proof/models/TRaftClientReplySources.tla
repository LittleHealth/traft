------------------------ MODULE TRaftClientReplySources ----------------------
EXTENDS TRaftClientPersistenceProof

ReplyHasDurableSource(m) == \E q \in calls :
    /\ q.id = m.id /\ m.sender \in Replicas
    /\ cache[m.sender][m.id].ready /\ m.value = cache[m.sender][m.id].value
ReplySources == \A m \in replyMessages : ReplyHasDurableSource(m)
ReturnedMessagesHaveSource == returned \subseteq replyMessages

THEOREM OnlySendReplyCreatesReplyMessages ==
    ASSUME ~MutReadWithoutBarrier, ClientAction
    PROVE (\E r \in Replicas : \E q \in calls : SendReply(r, q)) \/ UNCHANGED replyMessages
<1>1. Background => UNCHANGED replyMessages
    BY DEF Background
<1>2. \A q : Invoke(q) => UNCHANGED replyMessages
    BY DEF Invoke
<1>3. \A r, q : Admit(r, q) => UNCHANGED replyMessages
    BY DEF Admit, localClientVars
<1>4. \A r : ClosePartition(r) => UNCHANGED replyMessages
    BY DEF ClosePartition, localClientVars
<1>5. \A r, e : ApplyClient(r, e) => UNCHANGED replyMessages
    BY DEF ApplyClient
<1>6. \A m : ReceiveReply(m) => UNCHANGED replyMessages
    BY DEF ReceiveReply
<1>7. \A r, q : ~ReadWithoutBarrier(r, q)
    BY DEF ReadWithoutBarrier
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ClientAction

THEOREM ReplyMessagesNeverShrink ==
    ASSUME ~MutReadWithoutBarrier, ClientAction
    PROVE replyMessages \subseteq replyMessages'
<1>1. (\E r \in Replicas : \E q \in calls : SendReply(r, q)) \/ UNCHANGED replyMessages
    BY OnlySendReplyCreatesReplyMessages
<1> QED BY <1>1 DEF SendReply

THEOREM CallsNeverShrinkForReplySources == ClientAction => calls \subseteq calls'
<1>1. ClientAction => (\E q \in ClientCommands : Invoke(q)) \/ UNCHANGED <<calls, nextSequence>>
    BY OnlyInvocationChangesRequestIdentity
<1> QED BY <1>1 DEF Invoke

THEOREM ExistingReplySourcePersists ==
    ASSUME ReplySources, RequestIdentityState, CachedResultsPersist,
           calls \subseteq calls'
    PROVE \A m \in replyMessages : ReplyHasDurableSource(m)'
<1>1. ASSUME NEW m \in replyMessages
      PROVE ReplyHasDurableSource(m)'
    <2>1. PICK q \in calls : q.id = m.id /\ m.sender \in Replicas
              /\ cache[m.sender][m.id].ready /\ m.value = cache[m.sender][m.id].value
        BY DEF ReplySources, ReplyHasDurableSource
    <2>2. m.id \in RequestIds /\ q \in calls'
        BY <2>1 DEF RequestIdentityState, ClientCommands
    <2>3. cache'[m.sender][m.id] = cache[m.sender][m.id]
        BY <2>1, <2>2 DEF CachedResultsPersist
    <2> QED BY <2>1, <2>2, <2>3 DEF ReplyHasDurableSource
<1> QED BY <1>1

THEOREM NewReplyHasItsPersistentCacheSource ==
    ASSUME ~MutEarlyReply, NEW r \in Replicas, NEW q \in calls, SendReply(r, q)
    PROVE ReplyHasDurableSource([sender |-> r, id |-> q.id, value |-> cache[r][q.id].value])'
BY DEF SendReply, ReplyHasDurableSource

THEOREM ReplySourceInductiveStep ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ReplySources,
           RequestIdentityState, CachedResultsPersist, ClientAction
    PROVE ReplySources'
<1>1. calls \subseteq calls' /\ ((\E r \in Replicas : \E q \in calls : SendReply(r, q))
                                 \/ UNCHANGED replyMessages)
    BY CallsNeverShrinkForReplySources, OnlySendReplyCreatesReplyMessages
<1>2. \A m \in replyMessages : ReplyHasDurableSource(m)'
    BY ExistingReplySourcePersists, <1>1
<1>3. CASE UNCHANGED replyMessages
    BY <1>2, <1>3 DEF ReplySources
<1>4. CASE \E r \in Replicas : \E q \in calls : SendReply(r, q)
    <2>1. PICK r \in Replicas, q \in calls : SendReply(r, q)
        BY <1>4
    <2>2. replyMessages' = replyMessages \cup
              {[sender |-> r, id |-> q.id, value |-> cache[r][q.id].value]}
        BY <2>1 DEF SendReply
    <2>3. ReplyHasDurableSource([sender |-> r, id |-> q.id, value |-> cache[r][q.id].value])'
        BY NewReplyHasItsPersistentCacheSource, <2>1
    <2>4. UNCHANGED cache
        BY <2>1 DEF SendReply
    <2> QED BY <1>2, <2>2, <2>3, <2>4 DEF ReplySources
<1> QED BY <1>1, <1>3, <1>4

THEOREM OnlyReceivingAddsReturnedMessages == ClientAction =>
    (\E m \in replyMessages : ReceiveReply(m)) \/ UNCHANGED returned
BY DEF ClientAction, Background, Invoke, Admit, ClosePartition, localClientVars,
   ApplyClient, SendReply, ReadWithoutBarrier

THEOREM ReturnedSourceInductiveStep ==
    ASSUME ~MutReadWithoutBarrier, ReturnedMessagesHaveSource, ClientAction
    PROVE ReturnedMessagesHaveSource'
<1>1. replyMessages \subseteq replyMessages'
      /\ ((\E m \in replyMessages : ReceiveReply(m)) \/ UNCHANGED returned)
    BY ReplyMessagesNeverShrink, OnlyReceivingAddsReturnedMessages
<1> QED BY <1>1 DEF ReturnedMessagesHaveSource, ReceiveReply

THEOREM ClientRepliesHaveDurableSources ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => [](ReplySources /\ ReturnedMessagesHaveSource)
<1>1. ClientSpecification(Extra) => []RequestIdentityState /\ [][CachedResultsPersist]_cache
    BY PTL, ClientRequestIdentityAlways, ClientCachedResultsAlwaysPersist
<1>2. ClientInit => ReplySources /\ ReturnedMessagesHaveSource
    BY DEF ClientInit, ReplySources, ReturnedMessagesHaveSource
<1>3. ReplySources /\ ReturnedMessagesHaveSource /\ RequestIdentityState /\ [CachedResultsPersist]_cache
      /\ [ClientAction /\ Observe /\ Extra]_clientVars => ReplySources' /\ ReturnedMessagesHaveSource'
    BY ReplySourceInductiveStep, ReturnedSourceInductiveStep, CachePersistenceStutteringClosure
       DEF clientVars, localClientVars, ReplySources, ReplyHasDurableSource, ReturnedMessagesHaveSource
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification
=============================================================================
