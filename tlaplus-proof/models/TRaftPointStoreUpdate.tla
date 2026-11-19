------------------------- MODULE TRaftPointStoreUpdate -----------------------
EXTENDS TRaftPointStoreEvaluation, TRaftDeduplicatedCommutation

THEOREM SameFirstRequestsDetermineSamePointState ==
    ASSUME NEW A, NEW B, FirstRequestEntries(A) = FirstRequestEntries(B)
    PROVE AppliedPointState(A) = AppliedPointState(B)
<1>0. FirstRequestEntries(A) = FirstRequestEntries(B)
    OBVIOUS
<1>1. (\A id : RequestEntries(A, id) = RequestEntries(B, id))
      /\ (\A key : PointWrites(A, key) = PointWrites(B, key))
    BY ONLY <1>0 DEF RequestEntries, PointWrites
<1>2. \A key, p : PointWritesBefore(A, key, p) = PointWritesBefore(B, key, p)
    BY ONLY <1>1 DEF PointWritesBefore
<1>3. AppliedMachine(A) = AppliedMachine(B)
    BY ONLY <1>1 DEF AppliedMachine
<1>4. \A id \in RequestIds : AppliedCache(A)[id] = AppliedCache(B)[id]
    <2>1. ASSUME NEW id \in RequestIds
          PROVE AppliedCache(A)[id] = AppliedCache(B)[id]
        <3>1. RequestEntries(A, id) = RequestEntries(B, id)
            BY ONLY <1>1
        <3>2. (CHOOSE f \in RequestEntries(A, id) : TRUE)
                = (CHOOSE f \in RequestEntries(B, id) : TRUE)
            BY ONLY <3>1
        <3>3. DEFINE f == CHOOSE x \in RequestEntries(A, id) : TRUE
        <3>4. PointWritesBefore(A, f.value.key, f.part)
                = PointWritesBefore(B, f.value.key, f.part)
            BY ONLY <1>2
        <3> QED BY ONLY <2>1, <3>1, <3>2, <3>4 DEF AppliedCache, f
    <2> QED BY <2>1
<1>5. AppliedCache(A) = [id \in RequestIds |-> AppliedCache(A)[id]]
      /\ AppliedCache(B) = [id \in RequestIds |-> AppliedCache(B)[id]]
    BY AppliedInterpretationFunctionShapes
<1>6. AppliedCache(A) = AppliedCache(B)
    BY ONLY EqualFunctionValuesDetermineFunction, <1>4, <1>5
<1> QED BY ONLY <1>3, <1>6 DEF AppliedPointState

THEOREM FreshIdentityChangesRequestAndWriteSets ==
    ASSUME NEW A, NEW e \in Entries, e.kind = "data",
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE /\ \A id : RequestEntries(A \cup {e}, id) =
                IF id = e.value.id THEN {e} ELSE RequestEntries(A, id)
          /\ \A key : PointWrites(A \cup {e}, key) = PointWrites(A, key) \cup
                (IF key = e.value.key /\ e.value.op \in {"Put", "Delete"} THEN {e} ELSE {})
<1>1. FirstRequestEntries(A \cup {e}) = FirstRequestEntries(A) \cup {e}
      /\ \A f \in FirstRequestEntries(A) : f.value.id # e.value.id
    BY NewIdentityExtendsFirstRequests DEF FirstRequestEntries
<1> QED BY ZenonT(5), <1>1 DEF RequestEntries, PointWrites

THEOREM FreshIdentityPreservesEarlierWriteQueries ==
    ASSUME NEW A, NEW e \in Entries, e.kind = "data",
           \A f \in A : f.kind = "data" => f.value.id # e.value.id,
           NEW p \in Int, p <= e.part
    PROVE \A key : PointWritesBefore(A \cup {e}, key, p) = PointWritesBefore(A, key, p)
<1>1. \A key : PointWrites(A \cup {e}, key) = PointWrites(A, key) \cup
              (IF key = e.value.key /\ e.value.op \in {"Put", "Delete"} THEN {e} ELSE {})
    BY FreshIdentityChangesRequestAndWriteSets
<1>2. e.part \in Int /\ ~(e.part < p)
    BY SMT DEF Entries, Partitions
<1> QED BY SMT, <1>1, <1>2 DEF PointWritesBefore

THEOREM FreshRequestPreservesOtherCacheEntries ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries, e.kind = "data",
           \A f \in A : f.kind = "data" => f.value.id # e.value.id,
           \A f \in A : f.part <= e.part,
           NEW id \in RequestIds, id # e.value.id
    PROVE AppliedCache(A \cup {e})[id] = AppliedCache(A)[id]
<1>1. RequestEntries(A \cup {e}, id) = RequestEntries(A, id)
    BY FreshIdentityChangesRequestAndWriteSets
<1>2. CASE RequestEntries(A, id) = {}
    BY AppliedCacheAtEmptyIdentity, <1>1, <1>2
<1>3. CASE RequestEntries(A, id) # {}
    <2>1. DEFINE f == CHOOSE x \in RequestEntries(A, id) : TRUE
    <2>2. f \in RequestEntries(A, id) /\ f \in A
        BY ZenonT(5), <1>3 DEF f, RequestEntries, FirstRequestEntries
    <2>3. f.part \in Int /\ f.part <= e.part
        BY SMT, <2>2 DEF Entries, Partitions
    <2>4. PointWritesBefore(A \cup {e}, f.value.key, f.part)
            = PointWritesBefore(A, f.value.key, f.part)
        BY FreshIdentityPreservesEarlierWriteQueries, <2>3
    <2>5. (CHOOSE x \in RequestEntries(A \cup {e}, id) : TRUE) = f
        BY <1>1 DEF f
    <2>6. AppliedCache(A \cup {e})[id] = [ready |-> TRUE, value |->
              IF f.value.op = "Get" THEN LastWriteValue(PointWritesBefore(A \cup {e}, f.value.key, f.part)) ELSE "OK"]
          /\ AppliedCache(A)[id] = [ready |-> TRUE, value |->
              IF f.value.op = "Get" THEN LastWriteValue(PointWritesBefore(A, f.value.key, f.part)) ELSE "OK"]
        BY AppliedCacheAtPresentIdentity, <1>1, <1>3, <2>5 DEF f
    <2> QED BY ONLY <2>4, <2>6
<1> QED BY <1>2, <1>3

THEOREM FreshReadSeesAllEarlierAppliedWrites ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value.op = "Get", PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part,
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE PointWritesBefore(A \cup {e}, e.value.key, e.part) = PointWrites(A, e.value.key)
<1>1. \A f \in A : f.part < e.part
    BY NewReadHasNoSamePartitionPredecessor
<1>2. e.part \in Int
    BY DEF Entries, Partitions
<1>3. PointWritesBefore(A \cup {e}, e.value.key, e.part)
          = PointWritesBefore(A, e.value.key, e.part)
    BY FreshIdentityPreservesEarlierWriteQueries, <1>2
<1> QED BY SMT, <1>1, <1>3 DEF PointWritesBefore, PointWrites, FirstRequestEntries

THEOREM FreshRequestStoresItsSequentialReply ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value \in ClientCommands, PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part,
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE AppliedCache(A \cup {e})[e.value.id]
          = [ready |-> TRUE, value |-> Reply(AppliedMachine(A), e.value)]
<1>1. RequestEntries(A \cup {e}, e.value.id) = {e}
      /\ e.value.id \in RequestIds /\ e.value.key \in Keys
    BY FreshIdentityChangesRequestAndWriteSets DEF ClientCommands
<1>2. (CHOOSE f \in RequestEntries(A \cup {e}, e.value.id) : TRUE) = e
    BY ZenonT(5), <1>1
<1>20. AppliedCache(A \cup {e})[e.value.id] = [ready |-> TRUE, value |->
             IF e.value.op = "Get"
             THEN LastWriteValue(PointWritesBefore(A \cup {e}, e.value.key, e.part)) ELSE "OK"]
    BY AppliedCacheAtPresentIdentity, <1>1, <1>2
<1>3. CASE e.value.op = "Get"
    <2>1. PointWritesBefore(A \cup {e}, e.value.key, e.part) = PointWrites(A, e.value.key)
        BY FreshReadSeesAllEarlierAppliedWrites, <1>3
    <2>2. AppliedMachine(A)[e.value.key] = LastWriteValue(PointWrites(A, e.value.key))
        BY AppliedMachineAtKey, <1>1
    <2> QED BY ONLY <1>20, <1>3, <2>1, <2>2 DEF Reply
<1>4. CASE e.value.op # "Get"
    BY ONLY <1>20, <1>4 DEF Reply
<1> QED BY <1>3, <1>4

THEOREM FreshRequestUpdatesOneCacheRecord ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value \in ClientCommands, PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part,
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE AppliedCache(A \cup {e}) = [AppliedCache(A) EXCEPT ![e.value.id] =
                       [ready |-> TRUE, value |-> Reply(AppliedMachine(A), e.value)]]
<1>1. \A id \in RequestIds : id # e.value.id => AppliedCache(A \cup {e})[id] = AppliedCache(A)[id]
    BY FreshRequestPreservesOtherCacheEntries
<1>2. AppliedCache(A \cup {e})[e.value.id]
          = [ready |-> TRUE, value |-> Reply(AppliedMachine(A), e.value)]
    BY FreshRequestStoresItsSequentialReply
<1>3. e.value.id \in RequestIds
    BY DEF ClientCommands
<1>4. AppliedCache(A) = [id \in RequestIds |-> AppliedCache(A)[id]]
      /\ AppliedCache(A \cup {e}) = [id \in RequestIds |-> AppliedCache(A \cup {e})[id]]
    BY AppliedInterpretationFunctionShapes
<1>5. DEFINE G == [AppliedCache(A) EXCEPT ![e.value.id] =
                       [ready |-> TRUE, value |-> Reply(AppliedMachine(A), e.value)]]
<1>6. G = [id \in RequestIds |-> G[id]]
    BY FunctionUpdatePreservesDomainShape, <1>3, <1>4 DEF G
<1>7. \A id \in RequestIds : AppliedCache(A \cup {e})[id] = G[id]
    BY ONLY SMT, <1>1, <1>2, <1>3, <1>4 DEF G
<1> QED BY EqualFunctionValuesDetermineFunction, <1>4, <1>6, <1>7 DEF G

THEOREM NewWriteIsLaterThanEarlierWritesOfItsKey ==
    ASSUME NEW A, A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part
    PROVE \A f \in PointWrites(A, e.value.key) : f.part < e.part
<1>1. e.part \in Int /\ \A f \in A : f.part \in Int
    BY SMT DEF Entries, Partitions
<1>2. \A f \in PointWrites(A, e.value.key) :
          f \in A /\ f.kind = "data" /\ f.value.key = e.value.key /\ f # e
    BY SMT DEF PointWrites, FirstRequestEntries
<1> QED BY SMT, <1>1, <1>2 DEF PointLog

THEOREM FreshRequestHasSequentialMachineEffect ==
    ASSUME NEW A, IsFiniteSet(A), A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value \in ClientCommands, PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part,
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE AppliedMachine(A \cup {e}) = Effect(AppliedMachine(A), e.value)
<1>1. \A key : PointWrites(A \cup {e}, key) = PointWrites(A, key) \cup
              (IF key = e.value.key /\ e.value.op \in {"Put", "Delete"} THEN {e} ELSE {})
    BY FreshIdentityChangesRequestAndWriteSets
<1>2. PointWrites(A, e.value.key) \subseteq A
      /\ \A f \in PointWrites(A, e.value.key) : f.part < e.part
    BY NewWriteIsLaterThanEarlierWritesOfItsKey DEF PointWrites, FirstRequestEntries
<1>3. IsFiniteSet(PointWrites(A, e.value.key) \cup {e})
      /\ PointWrites(A, e.value.key) \cup {e} \subseteq Entries
    BY SMT, FS_Subset, FS_AddElement, <1>2
<1>4. LastWriteValue(PointWrites(A, e.value.key) \cup {e}) = WriteValue(e)
    BY UniqueLatestWriteDeterminesValue, <1>2, <1>3
<1>5. e.value.key \in Keys /\ e.value.op \in {"Put", "Delete", "Get"}
    BY DEF ClientCommands
<1>50. AppliedMachine(A) = [key \in Keys |-> AppliedMachine(A)[key]]
       /\ AppliedMachine(A \cup {e}) = [key \in Keys |-> AppliedMachine(A \cup {e})[key]]
    BY AppliedInterpretationFunctionShapes
<1>51. Effect(AppliedMachine(A), e.value) = [key \in Keys |-> Effect(AppliedMachine(A), e.value)[key]]
    BY PointEffectPreservesFunctionShape, <1>50
<1>6. ASSUME NEW key \in Keys
      PROVE AppliedMachine(A \cup {e})[key] = Effect(AppliedMachine(A), e.value)[key]
    <2>1. AppliedMachine(A \cup {e})[key] = LastWriteValue(PointWrites(A \cup {e}, key))
          /\ AppliedMachine(A)[key] = LastWriteValue(PointWrites(A, key))
        BY AppliedMachineAtKey
    <2>2. CASE e.value.op = "Get"
        <3>1. PointWrites(A \cup {e}, key) = PointWrites(A, key)
            BY ONLY <1>1, <2>2
        <3>2. Effect(AppliedMachine(A), e.value) = AppliedMachine(A)
            BY ONLY <2>2 DEF Effect
        <3> QED BY ONLY <2>1, <3>1, <3>2
    <2>3. CASE e.value.op = "Put" /\ key = e.value.key
        BY ONLY SMT, <1>1, <1>4, <1>50, <1>6, <2>1, <2>3 DEF Effect, WriteValue
    <2>4. CASE e.value.op = "Delete" /\ key = e.value.key
        BY ONLY SMT, <1>1, <1>4, <1>50, <1>6, <2>1, <2>4 DEF Effect, WriteValue
    <2>5. CASE key # e.value.key
        <3>1. PointWrites(A \cup {e}, key) = PointWrites(A, key)
            BY ONLY <1>1, <2>5
        <3>2. Effect(AppliedMachine(A), e.value)[key] = AppliedMachine(A)[key]
            BY ONLY SMT, <1>5, <1>50, <1>6, <2>5 DEF Effect
        <3> QED BY ONLY <2>1, <3>1, <3>2
    <2> QED BY ONLY SMT, <1>5, <2>2, <2>3, <2>4, <2>5
<1> QED BY EqualFunctionValuesDetermineFunction, <1>50, <1>51, <1>6

THEOREM FreshRequestInterpretationIsActualTransition ==
    ASSUME NEW A, IsFiniteSet(A), A \subseteq Entries, NEW e \in Entries,
           e \notin A, e.kind = "data", e.value \in ClientCommands, PointLog(A \cup {e}),
           \A f \in A : f.part <= e.part,
           \A f \in A : f.kind = "data" => f.value.id # e.value.id
    PROVE AppliedPointState(A \cup {e}) = PointTransition(AppliedPointState(A), e.value)
<1>1. AppliedMachine(A \cup {e}) = Effect(AppliedMachine(A), e.value)
      /\ AppliedCache(A \cup {e}) = [AppliedCache(A) EXCEPT ![e.value.id] =
                         [ready |-> TRUE, value |-> Reply(AppliedMachine(A), e.value)]]
    BY FreshRequestHasSequentialMachineEffect, FreshRequestUpdatesOneCacheRecord
<1>2. RequestEntries(A, e.value.id) = {} /\ e.value.id \in RequestIds
    BY SMT DEF RequestEntries, FirstRequestEntries, ClientCommands
<1>3. ~AppliedCache(A)[e.value.id].ready
    BY SMT, <1>2 DEF AppliedCache
<1> QED BY SMT, <1>1, <1>3 DEF AppliedPointState, PointTransition
=============================================================================
