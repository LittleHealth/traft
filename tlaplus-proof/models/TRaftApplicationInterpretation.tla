---------------------- MODULE TRaftApplicationInterpretation ----------------
EXTENDS TRaftPointStoreUpdate, TRaftClientApplicationProof

ApplicationLogFacts ==
    /\ TypeOK /\ AppliedEntriesPreserved /\ AppliedPrefixClosure /\ FiniteLogInvariant
    /\ RequestIdentityState
    /\ \A r \in Replicas : PointLog(formal[r])
    /\ \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls

THEOREM NewApplicationHasInterpretationInputs ==
    ASSUME ApplicationLogFacts, NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE /\ IsFiniteSet(applied[r]) /\ applied[r] \subseteq Entries /\ e \in Entries
          /\ e \notin applied[r] /\ PointLog(applied[r] \cup {e})
          /\ \A f \in applied[r] : f.part <= e.part
          /\ e.kind = "data" => e.value \in ClientCommands
<1>1. IsFiniteSet(formal[r]) /\ formal[r] \subseteq Entries
      /\ applied[r] \subseteq formal[r] /\ e \in formal[r] \ applied[r]
      /\ PointLog(formal[r])
    BY DEF ApplicationLogFacts, TypeOK, FiniteLogInvariant, FiniteNodeData,
       AppliedEntriesPreserved, ApplyClient, ApplyEntry
<1>2. IsFiniteSet(applied[r]) /\ PointLog(applied[r] \cup {e})
    BY SMT, FS_Subset, PointLogInheritedBySubset, <1>1
<1>3. \A f \in applied[r] : f.part <= e.part
    BY NewApplicationDoesNotGoBackwards DEF ApplicationLogFacts, ApplyClient
<1>4. applied[r] \subseteq Entries /\ e \in Entries /\ e \notin applied[r]
    BY ONLY SMT, <1>1
<1>5. e.kind = "data" => e.value \in ClientCommands
    BY <1>1 DEF PointLog
<1> QED BY ONLY <1>2, <1>3, <1>4, <1>5

THEOREM AppliedRetryHasStrictlyEarlierOccurrence ==
    ASSUME ApplicationLogFacts, ReadyIdsMatchApplied, NEW r \in Replicas, NEW e,
           ApplyClient(r, e), e.kind = "data", cache[r][e.value.id].ready
    PROVE \E f \in applied[r] : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part
<1>1. applied[r] \subseteq Entries /\ e \in Entries /\ e \notin applied[r]
      /\ PointLog(applied[r] \cup {e}) /\ (\A f \in applied[r] : f.part <= e.part)
      /\ e.value \in ClientCommands
    BY NewApplicationHasInterpretationInputs
<1>2. e.value.id \in RequestIds
    BY <1>1 DEF ClientCommands
<1>3. PICK f \in applied[r] : f.kind = "data" /\ f.value.id = e.value.id
    BY <1>2 DEF ReadyIdsMatchApplied
<1>4. f \in formal[r] /\ e \in formal[r]
      /\ f.value \in calls /\ e.value \in calls /\ RequestIdentityState
    BY <1>3 DEF ApplicationLogFacts, AppliedEntriesPreserved, ApplyClient, ApplyEntry
<1>5. f.value = e.value /\ f # e /\ f.part <= e.part
      /\ f.part \in Int /\ e.part \in Int
    BY SMT, <1>1, <1>3, <1>4 DEF RequestIdentityState, Entries, Partitions
<1>6. f.part < e.part
    BY SMT, <1>1, <1>3, <1>5 DEF PointLog
<1> QED BY <1>3, <1>6

THEOREM ApplyingClientPreservesInterpretation ==
    ASSUME ApplicationMatchesAppliedSet, ApplicationTypes, ReadyIdsMatchApplied,
           ApplicationLogFacts, NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE ApplicationMatchesAppliedSet'
<1>1. IsFiniteSet(applied[r]) /\ applied[r] \subseteq Entries /\ e \in Entries
      /\ e \notin applied[r] /\ PointLog(applied[r] \cup {e})
      /\ (\A f \in applied[r] : f.part <= e.part)
      /\ (e.kind = "data" => e.value \in ClientCommands)
    BY NewApplicationHasInterpretationInputs
<1>2. applied'[r] = applied[r] \cup {e}
      /\ \A s \in Replicas \ {r} :
           applied'[s] = applied[s] /\ machine'[s] = machine[s] /\ cache'[s] = cache[s]
    BY SMT DEF ApplyClient, ApplyEntry, ApplicationLogFacts, TypeOK, ApplicationTypes
<1>3. [db |-> machine[r], cache |-> cache[r]] = AppliedPointState(applied[r])
    BY DEF ApplicationMatchesAppliedSet, AppliedPointState
<1>4. e.kind \in {"noop", "data"}
    BY <1>1 DEF Entries
<1>5. CASE e.kind = "noop"
    <2>1. FirstRequestEntries(applied[r] \cup {e}) = FirstRequestEntries(applied[r])
        BY AddingNoopPreservesFirstRequests, <1>5
    <2>2. AppliedPointState(applied'[r]) = AppliedPointState(applied[r])
          /\ UNCHANGED <<machine, cache>>
        BY SameFirstRequestsDetermineSamePointState, <1>2, <1>5, <2>1 DEF ApplyClient
    <2> QED BY SMT, <1>2, <1>3, <2>2 DEF ApplicationMatchesAppliedSet, AppliedPointState
<1>6. CASE e.kind = "data" /\ cache[r][e.value.id].ready
    <2>1. \E f \in applied[r] : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part
        BY AppliedRetryHasStrictlyEarlierOccurrence, <1>6
    <2>2. FirstRequestEntries(applied[r] \cup {e}) = FirstRequestEntries(applied[r])
        BY LaterRetryPreservesFirstRequests, <1>1, <1>6, <2>1
    <2>3. AppliedPointState(applied'[r]) = AppliedPointState(applied[r])
          /\ UNCHANGED <<machine, cache>>
        BY SameFirstRequestsDetermineSamePointState, CachedRetryHasNoEffect, <1>2, <1>6, <2>2
    <2> QED BY SMT, <1>2, <1>3, <2>3 DEF ApplicationMatchesAppliedSet, AppliedPointState
<1>7. CASE e.kind = "data" /\ ~cache[r][e.value.id].ready
    <2>1. e.value.id \in RequestIds
          /\ \A f \in applied[r] : f.kind = "data" => f.value.id # e.value.id
        BY SMT, <1>1, <1>7 DEF ClientCommands, ReadyIdsMatchApplied
    <2>2. AppliedPointState(applied'[r]) = PointTransition(AppliedPointState(applied[r]), e.value)
        BY FreshRequestInterpretationIsActualTransition, <1>1, <1>2, <1>7, <2>1
    <2>3. [db |-> machine'[r], cache |-> cache'[r]] =
            PointTransition([db |-> machine[r], cache |-> cache[r]], e.value)
        BY ActualApplicationIsPointTransition, <1>1, <1>7 DEF ApplicationTypes
    <2> QED BY SMT, <1>2, <1>3, <2>2, <2>3 DEF ApplicationMatchesAppliedSet, AppliedPointState
<1> QED BY <1>4, <1>5, <1>6, <1>7

THEOREM ApplicationInterpretationInitially == ClientInit => ApplicationMatchesAppliedSet
BY SMT, EmptyAppliedState DEF ClientInit, Init, ApplicationMatchesAppliedSet, AppliedPointState

THEOREM ApplicationInterpretationInductiveStep ==
    ASSUME ~MutLoseDedup, ApplicationMatchesAppliedSet, ApplicationTypes,
           ReadyIdsMatchApplied, ApplicationLogFacts, ClientAction
    PROVE ApplicationMatchesAppliedSet'
<1>1. (\E r \in Replicas : \E e : ApplyClient(r, e))
       \/ UNCHANGED <<applied, machine, cache>>
    BY OnlyClientApplicationChangesPersistentApplication
<1>2. CASE \E r \in Replicas : \E e : ApplyClient(r, e)
    BY ApplyingClientPreservesInterpretation, <1>2
<1>3. CASE UNCHANGED <<applied, machine, cache>>
    BY <1>3 DEF ApplicationMatchesAppliedSet
<1> QED BY <1>1, <1>2, <1>3
=============================================================================
