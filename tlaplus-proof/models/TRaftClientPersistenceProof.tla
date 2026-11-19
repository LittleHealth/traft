---------------------- MODULE TRaftClientPersistenceProof --------------------
EXTENDS TRaftClientCore, TLAPS

RequestIdentityState ==
    /\ calls \subseteq ClientCommands
    /\ nextSequence \in [Clients -> Nat]
    /\ \A q \in calls : q.id[2] < nextSequence[q.id[1]]
    /\ \A q, p \in calls : q.id = p.id => q = p
CacheFunctions ==
    /\ cache = [r \in Replicas |-> cache[r]]
    /\ \A r \in Replicas : cache[r] = [id \in RequestIds |-> cache[r][id]]
CachedResultsPersist == \A r \in Replicas : \A id \in RequestIds :
    cache[r][id].ready => cache'[r][id] = cache[r][id]

THEOREM OnlyInvocationChangesRequestIdentity ==
    ClientAction => (\E q \in ClientCommands : Invoke(q)) \/ UNCHANGED <<calls, nextSequence>>
<1>1. Background => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF Background
<1>2. \A r, q : Admit(r, q) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF Admit, localClientVars
<1>3. \A r : ClosePartition(r) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF ClosePartition, localClientVars
<1>4. \A r, e : ApplyClient(r, e) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF ApplyClient
<1>5. \A r, q : SendReply(r, q) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF SendReply
<1>6. \A r, q : ReadWithoutBarrier(r, q) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF ReadWithoutBarrier
<1>7. \A m : ReceiveReply(m) => UNCHANGED <<calls, nextSequence>>
    BY SMT DEF ReceiveReply
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ClientAction

THEOREM InvocationPreservesRequestIdentity ==
    ASSUME RequestIdentityState, NEW q \in ClientCommands, Invoke(q)
    PROVE RequestIdentityState'
<1>1. q.id[1] \in Clients /\ q.id[2] \in Nat
      /\ q.id[2] = nextSequence[q.id[1]]
    BY SMT DEF Invoke, ClientCommands, RequestIds, SeqDomain
<1>2. \A p \in calls : p.id[1] \in Clients /\ p.id[2] \in Nat
    BY SMT DEF RequestIdentityState, ClientCommands, RequestIds, SeqDomain
<1>3. \A p \in calls : p.id # q.id
    BY SMT, <1>1, <1>2 DEF RequestIdentityState
<1>4. nextSequence' \in [Clients -> Nat]
      /\ \A c \in Clients : nextSequence[c] <= nextSequence'[c]
    BY SMT, <1>1 DEF RequestIdentityState, Invoke
<1>5. q.id[2] < nextSequence'[q.id[1]]
    BY SMT, <1>1 DEF Invoke, RequestIdentityState
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5 DEF RequestIdentityState, Invoke

THEOREM RequestIdentityInitially == ClientInit => RequestIdentityState
BY SMT DEF ClientInit, RequestIdentityState

THEOREM RequestIdentityInductiveStep ==
    ASSUME RequestIdentityState, ClientAction
    PROVE RequestIdentityState'
BY SMT, OnlyInvocationChangesRequestIdentity, InvocationPreservesRequestIdentity DEF RequestIdentityState

THEOREM ClientRequestIdentityAlways ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []RequestIdentityState
<1>1. ClientInit => RequestIdentityState
    BY RequestIdentityInitially
<1>2. RequestIdentityState /\ [ClientAction /\ Observe /\ Extra]_clientVars => RequestIdentityState'
    BY SMT, RequestIdentityInductiveStep DEF clientVars, localClientVars, RequestIdentityState
<1> QED BY PTL, <1>1, <1>2 DEF ClientSpecification

THEOREM OnlyApplicationChangesCache ==
    ASSUME ~MutLoseDedup, CacheFunctions, ClientAction
    PROVE (\E r \in Replicas : \E e : ApplyClient(r, e)) \/ UNCHANGED cache
<1>1. Background => UNCHANGED cache
    BY SMT DEF Background, CacheFunctions
<1>2. \A q : Invoke(q) => UNCHANGED cache
    BY SMT DEF Invoke
<1>3. \A r, q : Admit(r, q) => UNCHANGED cache
    BY SMT DEF Admit, localClientVars
<1>4. \A r : ClosePartition(r) => UNCHANGED cache
    BY SMT DEF ClosePartition, localClientVars
<1>5. \A r, q : SendReply(r, q) => UNCHANGED cache
    BY SMT DEF SendReply
<1>6. \A r, q : ReadWithoutBarrier(r, q) => UNCHANGED cache
    BY SMT DEF ReadWithoutBarrier
<1>7. \A m : ReceiveReply(m) => UNCHANGED cache
    BY SMT DEF ReceiveReply
<1>8. ClientAction
    OBVIOUS
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF ClientAction

THEOREM NestedUpdateAtKnownReplica ==
    ASSUME NEW N, NEW F, F = [r \in N |-> F[r]], NEW r \in N,
           NEW id, NEW value, NEW G, G = [F EXCEPT ![r][id] = value]
    PROVE G[r] = [F[r] EXCEPT ![id] = value]
BY SMT

THEOREM ApplicationPreservesCachedResults ==
    ASSUME CacheFunctions, NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE CacheFunctions' /\ CachedResultsPersist
<1>1. \A s \in Replicas \ {r} : cache'[s] = cache[s]
    BY SMT DEF ApplyClient, CacheFunctions
<1>2. cache'[r] = cache[r] \/
          (cache'[r] = [cache[r] EXCEPT ![e.value.id] = [ready |-> TRUE, value |-> Reply(machine[r], e.value)]]
            /\ ~cache[r][e.value.id].ready)
    <2>1. (cache' = cache) \/
              (cache' = [cache EXCEPT ![r][e.value.id] = [ready |-> TRUE, value |-> Reply(machine[r], e.value)]]
                /\ ~cache[r][e.value.id].ready)
        BY ZenonT(10) DEF ApplyClient
    <2>2. cache = [s \in Replicas |-> cache[s]] /\ r \in Replicas
        BY DEF CacheFunctions
    <2> QED BY ONLY SMT, <2>1, <2>2, NestedUpdateAtKnownReplica
<1>20. r \in Replicas /\ cache[r] = [id \in RequestIds |-> cache[r][id]]
    BY DEF CacheFunctions
<1>3. CachedResultsPersist
    BY ONLY SMT, <1>1, <1>2, <1>20 DEF CachedResultsPersist
<1>4. CacheFunctions'
    BY SMT DEF ApplyClient, CacheFunctions
<1> QED BY <1>3, <1>4

THEOREM CacheFunctionsInitially == ClientInit => CacheFunctions
BY SMT DEF ClientInit, EmptyCache, CacheFunctions

THEOREM CacheInductiveStep ==
    ASSUME ~MutLoseDedup, CacheFunctions, ClientAction
    PROVE CacheFunctions' /\ CachedResultsPersist
<1>1. (\E r \in Replicas : \E e : ApplyClient(r, e)) \/ UNCHANGED cache
    BY OnlyApplicationChangesCache
<1> QED BY SMT, <1>1, ApplicationPreservesCachedResults DEF CacheFunctions, CachedResultsPersist

THEOREM ClientCachedResultsAlwaysPersist ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => [][CachedResultsPersist]_cache
<1>1. ClientInit => CacheFunctions
    BY CacheFunctionsInitially
<1>2. CacheFunctions /\ [ClientAction /\ Observe /\ Extra]_clientVars =>
          CacheFunctions' /\ CachedResultsPersist
    BY SMT, CacheInductiveStep DEF CacheFunctions, CachedResultsPersist, clientVars, localClientVars
<1>3. ClientSpecification(Extra) => []CacheFunctions
    BY PTL, <1>1, <1>2 DEF ClientSpecification
<1> QED BY PTL, <1>2, <1>3 DEF ClientSpecification

\* Action properties under [] must be stuttering-closed TLA+ formulas.
\* Here closing on cache is equivalent to the original two-state predicate:
\* an unchanged cache preserves every ready result, without any type premise.
THEOREM CachePersistenceStutteringClosure ==
    [CachedResultsPersist]_cache <=> CachedResultsPersist
BY SMT DEF CachedResultsPersist

\* A ready record never changes or becomes unready. ApplyClient consults
\* exactly that durable record before applying a request. Agreement between
\* different replicas and the evidence-order witness remain separate goals.
THEOREM ReadyRequestCannotBeAppliedAgain ==
    ASSUME NEW r \in Replicas, NEW e, e.kind = "data",
           cache[r][e.value.id].ready, ApplyClient(r, e)
    PROVE UNCHANGED <<machine, cache>>
BY SMT DEF ApplyClient
=============================================================================
