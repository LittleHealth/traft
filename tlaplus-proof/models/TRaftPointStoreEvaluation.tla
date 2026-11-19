---------------------- MODULE TRaftPointStoreEvaluation ----------------------
EXTENDS TRaftPointStoreFacts, TRaftFunctionProof

THEOREM AppliedCacheAtEmptyIdentity ==
    ASSUME NEW A, NEW id \in RequestIds, RequestEntries(A, id) = {}
    PROVE AppliedCache(A)[id] = [ready |-> FALSE, value |-> Missing]
BY ZenonT(5) DEF AppliedCache

THEOREM AppliedCacheAtPresentIdentity ==
    ASSUME NEW A, NEW id \in RequestIds, RequestEntries(A, id) # {},
           NEW e, e = (CHOOSE f \in RequestEntries(A, id) : TRUE)
    PROVE AppliedCache(A)[id] = [ready |-> TRUE, value |->
        IF e.value.op = "Get" THEN LastWriteValue(PointWritesBefore(A, e.value.key, e.part)) ELSE "OK"]
BY ZenonT(5) DEF AppliedCache

THEOREM AppliedCacheRecordShape ==
    ASSUME NEW A, NEW id \in RequestIds
    PROVE AppliedCache(A)[id].ready \in BOOLEAN
          /\ AppliedCache(A)[id] = [ready |-> AppliedCache(A)[id].ready,
                                     value |-> AppliedCache(A)[id].value]
<1>1. CASE RequestEntries(A, id) = {}
    <2>1. AppliedCache(A)[id] = [ready |-> FALSE, value |-> Missing]
        BY AppliedCacheAtEmptyIdentity, <1>1
    <2> QED BY ONLY SMT, <2>1
<1>2. CASE RequestEntries(A, id) # {}
    <2>1. DEFINE e == CHOOSE f \in RequestEntries(A, id) : TRUE
    <2>2. AppliedCache(A)[id] = [ready |-> TRUE, value |->
            IF e.value.op = "Get" THEN LastWriteValue(PointWritesBefore(A, e.value.key, e.part)) ELSE "OK"]
        BY AppliedCacheAtPresentIdentity, <1>2 DEF e
    <2> QED BY ONLY SMT, <2>2
<1> QED BY <1>1, <1>2

THEOREM AppliedMachineAtKey ==
    ASSUME NEW A, NEW key \in Keys
    PROVE AppliedMachine(A)[key] = LastWriteValue(PointWrites(A, key))
BY DEF AppliedMachine

THEOREM AppliedInterpretationFunctionShapes ==
    ASSUME NEW A
    PROVE AppliedCache(A) = [id \in RequestIds |-> AppliedCache(A)[id]]
          /\ AppliedMachine(A) = [key \in Keys |-> AppliedMachine(A)[key]]
BY Isa DEF AppliedCache, AppliedMachine

THEOREM EqualFunctionValuesDetermineFunction ==
    ASSUME NEW N, NEW F, NEW G, F = [i \in N |-> F[i]], G = [i \in N |-> G[i]],
           \A i \in N : F[i] = G[i]
    PROVE F = G
<1>1. [i \in N |-> F[i]] = [i \in N |-> G[i]]
    BY SMT
<1> QED BY <1>1

THEOREM PointEffectPreservesFunctionShape ==
    ASSUME NEW F, F = [key \in Keys |-> F[key]], NEW q \in ClientCommands
    PROVE Effect(F, q) = [key \in Keys |-> Effect(F, q)[key]]
<1>1. q.key \in Keys /\ q.op \in {"Put", "Delete", "Get"}
    BY DEF ClientCommands
<1> QED BY FunctionUpdatePreservesDomainShape, <1>1 DEF Effect
=============================================================================
