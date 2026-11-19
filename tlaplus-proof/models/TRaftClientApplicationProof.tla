---------------------- MODULE TRaftClientApplicationProof --------------------
EXTENDS TRaftDeduplicatedCommutation, TRaftApplicationPrefixProof

ApplicationTypes ==
    /\ machine \in [Replicas -> [Keys -> Values \cup {Missing}]]
    /\ cache \in [Replicas -> [RequestIds ->
                       [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]]
ClientApplicationSources == \A r \in Replicas : \A e \in formal[r] :
    e.kind = "data" => e.value \in ClientCommands
ReadyIdsMatchApplied == \A r \in Replicas : \A id \in RequestIds :
    cache[r][id].ready <=>
        \E e \in applied[r] : e.kind = "data" /\ e.value.id = id

THEOREM PointTransitionRecordsExactlyItsRequest ==
    ASSUME NEW s \in PointStates, NEW q \in ClientCommands
    PROVE \A id \in RequestIds :
        PointTransition(s, q).cache[id].ready <=> (s.cache[id].ready \/ id = q.id)
<1>1. q.id \in RequestIds
    BY DEF ClientCommands
<1> QED BY SMT, <1>1 DEF PointStates, PointTransition

THEOREM ApplicationTypesInitially == ClientInit => ApplicationTypes /\ ReadyIdsMatchApplied
BY SMT DEF ClientInit, Init, EmptyMachine, EmptyCache, ApplicationTypes, ReadyIdsMatchApplied

THEOREM ApplyingClientPreservesApplicationTypes ==
    ASSUME ApplicationTypes, ClientApplicationSources, TypeOK,
           NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE ApplicationTypes'
<1>1. e \in formal[r] /\ e.kind \in {"noop", "data"}
      /\ (e.kind = "data" => e.value \in ClientCommands)
    BY SMT DEF ApplyClient, ApplyEntry, TypeOK, Entries, ClientApplicationSources
<1>2. CASE e.kind = "noop"
    BY <1>2 DEF ApplyClient, ApplicationTypes
<1>3. CASE e.kind = "data"
    <2>1. e.value \in ClientCommands
        BY <1>1, <1>3
    <2>2. Effect(machine[r], e.value) \in [Keys -> Values \cup {Missing}]
          /\ Reply(machine[r], e.value) \in Values \cup {Missing, "OK"}
        BY SMT, <2>1 DEF ApplicationTypes, ClientCommands, Effect, Reply
    <2>3. machine \in [Replicas -> [Keys -> Values \cup {Missing}]]
          /\ cache \in [Replicas -> [RequestIds ->
                       [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]]
          /\ e.value.id \in RequestIds
        BY <2>1 DEF ApplicationTypes, ClientCommands
    <2>4. [cache[r] EXCEPT ![e.value.id] =
                  [ready |-> TRUE, value |-> Reply(machine[r], e.value)]]
            \in [RequestIds -> [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]
        BY ONLY SMT, <2>2, <2>3
    <2>5. [machine EXCEPT ![r] = Effect(machine[r], e.value)]
              \in [Replicas -> [Keys -> Values \cup {Missing}]]
          /\ [cache EXCEPT ![r] = [cache[r] EXCEPT ![e.value.id] =
                         [ready |-> TRUE, value |-> Reply(machine[r], e.value)]]]
              \in [Replicas -> [RequestIds ->
                       [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]]
        BY ONLY SMT, <2>2, <2>3, <2>4
    <2> QED BY <1>3, <2>3, <2>5 DEF ApplicationTypes, ApplyClient
<1> QED BY <1>1, <1>2, <1>3

THEOREM ApplyingClientPreservesReadyIds ==
    ASSUME ApplicationTypes, ReadyIdsMatchApplied, ClientApplicationSources, TypeOK,
           NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE ReadyIdsMatchApplied'
<1>1. e \in formal[r] /\ e.kind \in {"noop", "data"}
      /\ applied'[r] = applied[r] \cup {e}
      /\ \A s \in Replicas \ {r} : applied'[s] = applied[s] /\ cache'[s] = cache[s]
    BY SMT DEF ApplyClient, ApplyEntry, TypeOK, Entries, ApplicationTypes
<1>2. CASE e.kind = "noop"
    BY SMT, <1>1, <1>2 DEF ApplyClient, ReadyIdsMatchApplied
<1>3. CASE e.kind = "data"
    <2>1. e.value \in ClientCommands
          /\ [db |-> machine[r], cache |-> cache[r]] \in PointStates
        BY <1>1, <1>3 DEF ClientApplicationSources, ApplicationTypes, PointStates
    <2>2. [db |-> machine'[r], cache |-> cache'[r]] =
            PointTransition([db |-> machine[r], cache |-> cache[r]], e.value)
        BY ActualApplicationIsPointTransition, <1>3, <2>1 DEF ApplicationTypes
    <2>3. \A id \in RequestIds : cache'[r][id].ready <=>
               (cache[r][id].ready \/ id = e.value.id)
        BY PointTransitionRecordsExactlyItsRequest, <2>1, <2>2
    <2> QED BY SMT, <1>1, <1>3, <2>3 DEF ReadyIdsMatchApplied
<1> QED BY <1>1, <1>2, <1>3

THEOREM AdministrativeActionsDoNotApply == AdministrativeNext => UNCHANGED applied
<1>1. \A c : StartElection(c) => UNCHANGED applied
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED applied
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED applied
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED applied
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED applied
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED applied
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED applied
    BY SMT DEF DeliverReport
<1>8. \A c, selected : BuildRecovery(c, selected) => UNCHANGED applied
    BY SMT DEF BuildRecovery
<1>9. \A c, e : SendEntry(c, e) => UNCHANGED applied
    BY SMT DEF SendEntry
<1>10. \A r, o : ReceiveEntry(r, o) => UNCHANGED applied
    BY SMT DEF ReceiveEntry
<1>11. \A r, o : AckEntry(r, o) => UNCHANGED applied
    BY SMT DEF AckEntry
<1>12. \A r, source, p, e : CopyProposalEntry(r, source, p, e) => UNCHANGED applied
    BY SMT DEF CopyProposalEntry
<1>13. \A r, p : RetainProposal(r, p) => UNCHANGED applied
    BY SMT DEF RetainProposal
<1>14. \A r, p : AckProposal(r, p) => UNCHANGED applied
    BY SMT DEF AckProposal
<1>15. \A c, m : DeliverAck(c, m) => UNCHANGED applied
    BY SMT DEF DeliverAck
<1>16. \A c : ConfirmProposal(c) => UNCHANGED applied
    BY SMT DEF ConfirmProposal
<1>17. \A r, p : LearnConfirmation(r, p) => UNCHANGED applied
    BY SMT DEF LearnConfirmation
<1>18. \A c, e : CommitEntry(c, e) => UNCHANGED applied
    BY SMT DEF CommitEntry
<1>19. \A c, e : AdvertiseCommit(c, e) => UNCHANGED applied
    BY SMT DEF AdvertiseCommit
<1>20. \A r, m : LearnCommit(r, m) => UNCHANGED applied
    BY SMT DEF LearnCommit
<1>21. \A c : Activate(c) => UNCHANGED applied
    BY SMT DEF Activate
<1>22. \A r : Crash(r) => UNCHANGED applied
    BY SMT DEF Crash
<1>23. \A r : Restart(r) => UNCHANGED applied
    BY SMT DEF Restart
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23 DEF AdministrativeNext

THEOREM OnlyClientApplicationChangesPersistentApplication ==
    ASSUME ~MutLoseDedup, ApplicationTypes, ClientAction
    PROVE (\E r \in Replicas : \E e : ApplyClient(r, e))
       \/ UNCHANGED <<applied, machine, cache>>
<1>1. Background => UNCHANGED <<applied, machine, cache>>
    BY AdministrativeActionsDoNotApply, CrashAndRecoveryPreserveClientPersistence
       DEF Background, ApplicationTypes
<1>2. \A q : Invoke(q) => UNCHANGED <<applied, machine, cache>>
    BY SMT DEF Invoke, protocolVars
<1>3. \A r, q : Admit(r, q) => UNCHANGED <<applied, machine, cache>>
    BY SMT DEF Admit, CreateEntry, CreateSuccessor, localClientVars
<1>4. \A r : ClosePartition(r) => UNCHANGED <<applied, machine, cache>>
    BY SMT DEF ClosePartition, CreateSuccessor, localClientVars
<1>5. \A r, q : (SendReply(r, q) \/ ReadWithoutBarrier(r, q)) =>
          UNCHANGED <<applied, machine, cache>>
    BY SMT DEF SendReply, ReadWithoutBarrier, protocolVars
<1>6. \A m : ReceiveReply(m) => UNCHANGED <<applied, machine, cache>>
    BY SMT DEF ReceiveReply, protocolVars
<1>7. ClientAction
    OBVIOUS
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ClientAction

THEOREM ClientApplicationFactsInductiveStep ==
    ASSUME ~MutLoseDedup, ApplicationTypes, ReadyIdsMatchApplied,
           ClientApplicationSources, TypeOK, ClientAction
    PROVE ApplicationTypes' /\ ReadyIdsMatchApplied'
<1>1. (\E r \in Replicas : \E e : ApplyClient(r, e))
       \/ UNCHANGED <<applied, machine, cache>>
    BY OnlyClientApplicationChangesPersistentApplication
<1>2. CASE \E r \in Replicas : \E e : ApplyClient(r, e)
    BY ApplyingClientPreservesApplicationTypes, ApplyingClientPreservesReadyIds, <1>2
<1>3. CASE UNCHANGED <<applied, machine, cache>>
    BY <1>3 DEF ApplicationTypes, ReadyIdsMatchApplied
<1> QED BY <1>1, <1>2, <1>3

THEOREM ReadyIdentityHasTheOriginalCommand ==
    ASSUME ReadyIdsMatchApplied, RequestIdentityState, AppliedEntriesPreserved,
           \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls
    PROVE CacheHasAppliedRequest
<1>1. ASSUME NEW r \in Replicas, NEW q \in calls, cache[r][q.id].ready
      PROVE \E e \in applied[r] : e.kind = "data" /\ e.value = q
    <2>1. q.id \in RequestIds
        BY <1>1 DEF RequestIdentityState, ClientCommands
    <2>2. PICK e \in applied[r] : e.kind = "data" /\ e.value.id = q.id
        BY <1>1, <2>1 DEF ReadyIdsMatchApplied
    <2>3. e.value \in calls
        BY <1>1, <2>2 DEF AppliedEntriesPreserved
    <2>4. e.value = q
        BY <1>1, <2>2, <2>3 DEF RequestIdentityState
    <2> QED BY <2>2, <2>4
<1> QED BY <1>1 DEF CacheHasAppliedRequest
=============================================================================
