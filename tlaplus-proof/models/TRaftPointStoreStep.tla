-------------------------- MODULE TRaftPointStoreStep ------------------------
EXTENDS TRaftPointStoreUpdate
Least == INSTANCE NaturalsInduction

EntryPointStep(s, e) == IF e.kind = "data" THEN PointTransition(s, e.value) ELSE s

THEOREM OccurringRequestHasAFirstEntry ==
    ASSUME NEW A, A \subseteq Entries, NEW id,
           \E e \in A : e.kind = "data" /\ e.value.id = id
    PROVE RequestEntries(A, id) # {}
<1>1. DEFINE P(n) == \E e \in A : e.kind = "data" /\ e.value.id = id /\ e.part = n
<1>2. PICK e \in A : e.kind = "data" /\ e.value.id = id
    OBVIOUS
<1>3. e.part \in Nat /\ P(e.part)
    BY SMT, <1>2 DEF Entries, Partitions, P
<1> HIDE DEF P
<1>4. PICK m \in Nat : P(m) /\ \A k \in 0..(m - 1) : ~P(k)
    BY ONLY Least!SmallestNatural, <1>3, IsaM("blast")
<1>5. PICK f \in A : f.kind = "data" /\ f.value.id = id /\ f.part = m
    BY <1>4 DEF P
<1>6. \A x \in A : x.part \in Nat
    BY DEF Entries, Partitions
<1>7. f \in RequestEntries(A, id)
    <2>1. ASSUME NEW x \in A, x.kind = "data", x.value.id = f.value.id,
                x.part < f.part
          PROVE FALSE
        <3>1. x.part \in 0..(m - 1)
            BY ONLY SMT, <1>5, <1>6, <2>1
        <3>2. P(x.part)
            BY ONLY <1>5, <2>1 DEF P
        <3> QED BY ONLY <1>4, <3>1, <3>2
    <2> QED BY ONLY <1>5, <2>1 DEF RequestEntries, FirstRequestEntries
<1> QED BY <1>7

THEOREM InterpretedCacheReadyIffRequestOccurred ==
    ASSUME NEW A, A \subseteq Entries, NEW id \in RequestIds
    PROVE AppliedCache(A)[id].ready <=> \E e \in A : e.kind = "data" /\ e.value.id = id
<1>1. (\E e \in A : e.kind = "data" /\ e.value.id = id) => RequestEntries(A, id) # {}
    BY OccurringRequestHasAFirstEntry
<1>2. RequestEntries(A, id) # {} => \E e \in A : e.kind = "data" /\ e.value.id = id
    BY DEF RequestEntries, FirstRequestEntries
<1> QED BY SMT, <1>1, <1>2 DEF AppliedCache

THEOREM PreviouslySeenRequestHasEarlierPartition ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries, e.kind = "data", e \notin A,
           PointLog(A \cup {e}), RequestIdentityState,
           \A f \in A \cup {e} : f.kind = "data" => f.value \in calls,
           \A f \in A : f.part <= e.part,
           \E f \in A : f.kind = "data" /\ f.value.id = e.value.id
    PROVE \E f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part
<1>1. PICK f \in A : f.kind = "data" /\ f.value.id = e.value.id
    OBVIOUS
<1>2. f.value = e.value /\ f # e /\ f.part <= e.part
      /\ f.part \in Int /\ e.part \in Int
    BY SMT, <1>1 DEF RequestIdentityState, Entries, Partitions
<1>3. f.part # e.part
    BY SameRequestInOnePartitionIsOneEntry, <1>1, <1>2
<1> QED BY SMT, <1>1, <1>2, <1>3

THEOREM OrderedSetExtensionIsPointStep ==
    ASSUME NEW A, IsFiniteSet(A), A \subseteq Entries, NEW e \in Entries, e \notin A,
           PointLog(A \cup {e}), RequestIdentityState,
           \A f \in A \cup {e} : f.kind = "data" => f.value \in calls,
           \A f \in A : f.part <= e.part
    PROVE AppliedPointState(A \cup {e}) = EntryPointStep(AppliedPointState(A), e)
<1>1. e.kind \in {"noop", "data"}
      /\ (e.kind = "data" => e.value \in ClientCommands /\ e.value.id \in RequestIds)
    BY SMT DEF Entries, RequestIdentityState, ClientCommands
<1>2. CASE e.kind = "noop"
    <2>1. FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A)
        BY AddingNoopPreservesFirstRequests, <1>2
    <2> QED BY SameFirstRequestsDetermineSamePointState, <1>2, <2>1 DEF EntryPointStep
<1>3. CASE e.kind = "data" /\ \E f \in A : f.kind = "data" /\ f.value.id = e.value.id
    <2>1. \E f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part
        BY PreviouslySeenRequestHasEarlierPartition, <1>3
    <2>2. FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A)
        BY LaterRetryPreservesFirstRequests, <1>3, <2>1
    <2>3. AppliedCache(A)[e.value.id].ready
        BY InterpretedCacheReadyIffRequestOccurred, <1>1, <1>3
    <2> QED BY SameFirstRequestsDetermineSamePointState, <1>3, <2>2, <2>3
        DEF EntryPointStep, PointTransition, AppliedPointState
<1>4. CASE e.kind = "data" /\ ~\E f \in A : f.kind = "data" /\ f.value.id = e.value.id
    BY FreshRequestInterpretationIsActualTransition, <1>1, <1>4 DEF EntryPointStep
<1> QED BY <1>1, <1>2, <1>3, <1>4
=============================================================================
