-------------------------- MODULE TRaftPointStoreFacts -----------------------
EXTENDS TRaftPointStoreState, TRaftPointPartitionProof, TRaftClientPersistenceProof

THEOREM FirstEntriesAreAppliedData ==
    ASSUME NEW A
    PROVE FirstRequestEntries(A) \subseteq A
       /\ \A e \in FirstRequestEntries(A) : e.kind = "data"
BY DEF FirstRequestEntries

THEOREM SameRequestInOnePartitionIsOneEntry ==
    ASSUME NEW A, PointLog(A), RequestIdentityState,
           \A e \in A : e.kind = "data" => e.value \in calls,
           NEW e \in A, NEW f \in A, e.kind = "data", f.kind = "data",
           e.value.id = f.value.id, e.part = f.part
    PROVE e = f
<1>1. e.value \in calls /\ f.value \in calls /\ e.value = f.value
    BY DEF RequestIdentityState
<1> QED BY SMT, <1>1 DEF PointLog

THEOREM FirstRequestIdentityIsUnique ==
    ASSUME NEW A, A \subseteq Entries, PointLog(A), RequestIdentityState,
           \A e \in A : e.kind = "data" => e.value \in calls,
           NEW e \in FirstRequestEntries(A), NEW f \in FirstRequestEntries(A),
           e.value.id = f.value.id
    PROVE e = f
<1>1. e \in A /\ f \in A /\ e.kind = "data" /\ f.kind = "data"
      /\ e.part \in Int /\ f.part \in Int /\ ~(e.part < f.part) /\ ~(f.part < e.part)
    BY SMT DEF FirstRequestEntries, Entries, Partitions
<1>2. e.part = f.part
    BY ONLY SMT, <1>1
<1> QED BY SameRequestInOnePartitionIsOneEntry, <1>1, <1>2

THEOREM AddingNoopPreservesFirstRequests ==
    ASSUME NEW A, NEW e, e.kind = "noop"
    PROVE FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A)
BY SMT DEF FirstRequestEntries

THEOREM NewIdentityExtendsFirstRequests ==
    ASSUME NEW A, NEW e \in Entries, e.kind = "data",
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A) \cup {e}
BY SMT DEF FirstRequestEntries, Entries, Partitions

THEOREM LaterRetryPreservesFirstRequests ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries, e.kind = "data",
           \A f \in A : f.part <= e.part,
           \E f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part
    PROVE FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A)
<1>1. e.part \in Int /\ \A f \in A : f.part \in Int /\ f.part <= e.part
    BY SMT DEF Entries, Partitions
<1> QED BY SMT, <1>1 DEF FirstRequestEntries

THEOREM NewReadHasNoSamePartitionPredecessor ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value.op = "Get", PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part
    PROVE \A f \in A : f.part < e.part
<1>1. Part(A \cup {e}, e.part) = {e}
    BY DEF PointLog
<1>2. e.part \in Int /\ \A f \in A : f.part \in Int
    BY SMT DEF Entries, Partitions
<1> QED BY SMT, <1>1, <1>2 DEF Part

THEOREM LastWriteChoiceHasARealSource ==
    ASSUME NEW W, IsFiniteSet(W), W \subseteq Entries, W # {}
    PROVE (CHOOSE e \in W : e.part = Cur(W)) \in W
<1>1. \E e \in W : e.part = Cur(W)
    BY FiniteLogFrontier
<1> QED BY ZenonT(5), <1>1

THEOREM UniqueLatestWriteDeterminesValue ==
    ASSUME NEW W, IsFiniteSet(W), W \subseteq Entries, NEW e \in W,
           \A f \in W \ {e} : f.part < e.part
    PROVE LastWriteValue(W) = WriteValue(e)
<1>1. Cur(W) \in {f.part : f \in W}
      /\ \A f \in W : f.part <= Cur(W)
    BY FiniteLogFrontier
<1>2. e.part \in Int /\ \A f \in W : f.part \in Int
    BY SMT DEF Entries, Partitions
<1>3. Cur(W) = e.part /\ \A f \in W : f.part = Cur(W) => f = e
    BY SMT, <1>1, <1>2
<1>4. (CHOOSE f \in W : f.part = Cur(W)) = e
    BY ZenonT(5), <1>3
<1> QED BY <1>4 DEF LastWriteValue

THEOREM EmptyAppliedState ==
    AppliedPointState({}) = [db |-> EmptyMachine, cache |-> EmptyCache]
BY SMT DEF AppliedPointState, AppliedMachine, AppliedCache, EmptyMachine, EmptyCache,
   FirstRequestEntries, RequestEntries, PointWrites, LastWriteValue

THEOREM EarlierFirstRequestsDependOnlyOnEarlierEntries ==
    ASSUME NEW A, A \subseteq Entries, NEW p \in Int
    PROVE FirstRequestEntries(Prefix(A, p - 1))
          = {e \in FirstRequestEntries(A) : e.part < p}
<1>1. \A e \in A : e.part \in Int
    BY DEF Entries, Partitions
<1> QED BY SMT, <1>1 DEF FirstRequestEntries, Prefix

THEOREM EarlierWritesDependOnlyOnEarlierEntries ==
    ASSUME NEW A, A \subseteq Entries, NEW p \in Int, NEW key
    PROVE PointWritesBefore(A, key, p) = PointWrites(Prefix(A, p - 1), key)
<1>1. FirstRequestEntries(Prefix(A, p - 1))
          = {e \in FirstRequestEntries(A) : e.part < p}
    BY EarlierFirstRequestsDependOnlyOnEarlierEntries
<1> QED BY SMT, <1>1 DEF PointWritesBefore, PointWrites

THEOREM EqualAppliedSetsDetermineEqualApplication ==
    ASSUME ApplicationMatchesAppliedSet, NEW r \in Replicas, NEW s \in Replicas,
           applied[r] = applied[s]
    PROVE machine[r] = machine[s] /\ cache[r] = cache[s]
BY DEF ApplicationMatchesAppliedSet
=============================================================================
