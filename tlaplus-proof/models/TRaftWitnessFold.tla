-------------------------- MODULE TRaftWitnessFold ---------------------------
EXTENDS TRaftWitnessStep, TRaftPointStoreStep

THEOREM OrderPrefixesCompose ==
    ASSUME NEW a \in Seq(RequestIds), NEW b \in Seq(RequestIds), NEW c \in Seq(RequestIds),
           OrderPrefix(a, b), OrderPrefix(b, c)
    PROVE OrderPrefix(a, c)
<1>1. Len(a) \in Nat /\ Len(b) \in Nat /\ Len(c) \in Nat
    BY LenProperties
<1> QED BY SMT, <1>1 DEF OrderPrefix

THEOREM FoldingEvidenceKeepsSequentialWitness ==
    ASSUME RequestIdentityState, NEW S, \A e \in S : e.value \in calls,
           NEW order \in Seq(S), NEW initial \in WitnessStates,
           UniqueOrder(initial.order), WitnessSequential(initial)
    PROVE LET result == Fold(order, initial, LinearizationEntryStep)
          IN /\ result \in WitnessStates /\ UniqueOrder(result.order)
             /\ OrderPrefix(initial.order, result.order) /\ WitnessSequential(result)
<1>0. order \in Seq(S)
    OBVIOUS
<1>1. DEFINE P(s) == s \in WitnessStates /\ UniqueOrder(s.order)
                     /\ OrderPrefix(initial.order, s.order) /\ WitnessSequential(s)
<1>2. initial.order \in Seq(RequestIds) /\ Len(initial.order) \in Nat
    BY LenProperties DEF WitnessStates
<1>3. P(initial)
    BY <1>2 DEF P, OrderPrefix
<1>4. ASSUME NEW s, NEW e \in S, P(s)
      PROVE P(LinearizationEntryStep(s, e))
    <2>1. s \in WitnessStates /\ UniqueOrder(s.order) /\ WitnessSequential(s)
          /\ s.order \in Seq(RequestIds) /\ OrderPrefix(initial.order, s.order)
          /\ e.value \in calls /\ e.value \in ClientCommands
        BY <1>4 DEF P, WitnessStates, RequestIdentityState
    <2>2. LinearizationEntryStep(s, e) \in WitnessStates
          /\ UniqueOrder(LinearizationEntryStep(s, e).order)
          /\ OrderPrefix(s.order, LinearizationEntryStep(s, e).order)
          /\ WitnessSequential(LinearizationEntryStep(s, e))
        BY LinearizationStepHasTypedUniqueOrder, LinearizationStepKeepsSequentialExecution, <2>1
    <2>3. LinearizationEntryStep(s, e).order \in Seq(RequestIds)
        BY <2>2 DEF WitnessStates
    <2>4. OrderPrefix(initial.order, LinearizationEntryStep(s, e).order)
        BY OrderPrefixesCompose, <1>2, <2>1, <2>2, <2>3
    <2> QED BY <2>2, <2>4 DEF P
<1> HIDE DEF P
<1>5. P(Fold(order, initial, LinearizationEntryStep))
    BY ONLY FoldPreservesStatePredicate, <1>0, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>5 DEF P

THEOREM FoldingEvidenceSimulatesApplication ==
    ASSUME NEW S, \A e \in S : e.kind = "data" /\ e.value \in ClientCommands,
           NEW order \in Seq(S), NEW initial \in WitnessStates, UniqueOrder(initial.order),
           NEW point, WitnessPoint(initial) = point
    PROVE WitnessPoint(Fold(order, initial, LinearizationEntryStep))
            = Fold(order, point, EntryPointStep)
<1>0. order \in Seq(S)
    OBVIOUS
<1>1. DEFINE R(s, p) == s \in WitnessStates /\ UniqueOrder(s.order) /\ WitnessPoint(s) = p
<1>2. R(initial, point)
    BY DEF R
<1>3. ASSUME NEW s, NEW p, NEW e \in S, R(s, p)
      PROVE R(LinearizationEntryStep(s, e), EntryPointStep(p, e))
    <2>1. s \in WitnessStates /\ UniqueOrder(s.order) /\ WitnessPoint(s) = p
          /\ e.kind = "data" /\ e.value \in ClientCommands
        BY <1>3 DEF R
    <2>2. LinearizationEntryStep(s, e) \in WitnessStates
          /\ UniqueOrder(LinearizationEntryStep(s, e).order)
          /\ WitnessPoint(LinearizationEntryStep(s, e)) = PointTransition(WitnessPoint(s), e.value)
        BY LinearizationStepHasTypedUniqueOrder, LinearizationStepSimulatesDeduplicatedPointStep, <2>1
    <2> QED BY <2>1, <2>2 DEF R, EntryPointStep
<1> HIDE DEF R
<1>4. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>5. DEFINE K(n) == n <= Len(order) =>
          R(FoldTrace(order, initial, LinearizationEntryStep)[n],
            FoldTrace(order, point, EntryPointStep)[n])
<1>6. K(0)
    BY FoldTraceStartsAtInitial, <1>0, <1>2 DEF K
<1>7. ASSUME NEW n \in Nat, K(n)
      PROVE K(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE R(FoldTrace(order, initial, LinearizationEntryStep)[n + 1],
                          FoldTrace(order, point, EntryPointStep)[n + 1])
        BY DEF K
    <2>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
          /\ order[n + 1] \in S /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>4, <1>7, <2>1
    <2>3. R(FoldTrace(order, initial, LinearizationEntryStep)[n],
            FoldTrace(order, point, EntryPointStep)[n])
        BY <1>7, <2>2 DEF K
    <2>4. FoldTrace(order, initial, LinearizationEntryStep)[n + 1]
              = LinearizationEntryStep(FoldTrace(order, initial, LinearizationEntryStep)[n], order[n + 1])
          /\ FoldTrace(order, point, EntryPointStep)[n + 1]
              = EntryPointStep(FoldTrace(order, point, EntryPointStep)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <1>3, <2>2, <2>3, <2>4
<1> HIDE DEF K
<1>8. \A n \in Nat : K(n)
    BY ONLY NI!NatInduction, <1>6, <1>7, IsaM("blast")
<1>9. R(Fold(order, initial, LinearizationEntryStep), Fold(order, point, EntryPointStep))
    BY <1>4, <1>8 DEF K, Fold
<1> QED BY <1>9 DEF R

THEOREM WitnessInterpretationDeterminesIdentitySet ==
    ASSUME NEW s \in WitnessStates, NEW A, A \subseteq Entries,
           \A e \in A : e.kind = "data" => e.value \in ClientCommands,
           WitnessPoint(s) = AppliedPointState(A)
    PROVE Ids(s.order) = {e.value.id : e \in {x \in A : x.kind = "data"}}
<1>1. s.order \in Seq(RequestIds) /\ Ids(s.order) \subseteq RequestIds
      /\ {e.value.id : e \in {x \in A : x.kind = "data"}} \subseteq RequestIds
    BY LenProperties DEF WitnessStates, Ids, ClientCommands
<1>2. WitnessCache(s) = AppliedCache(A)
    BY SMT DEF WitnessPoint, AppliedPointState
<1>3. \A id \in RequestIds : WitnessCache(s)[id].ready = (id \in Ids(s.order))
    BY ONLY SMT DEF WitnessCache
<1>4. \A id \in RequestIds : id \in Ids(s.order) <=> AppliedCache(A)[id].ready
    <2>1. ASSUME NEW id \in RequestIds
          PROVE id \in Ids(s.order) <=> AppliedCache(A)[id].ready
        <3>1. WitnessCache(s)[id] = AppliedCache(A)[id]
            BY ONLY ZenonT(5), <1>2
        <3>2. AppliedCache(A)[id].ready = (id \in Ids(s.order))
            BY ONLY ZenonT(5), <1>3, <2>1, <3>1
        <3> QED BY ONLY ZenonT(5), <3>2
    <2> QED BY ONLY <2>1
<1>5. \A id \in RequestIds : AppliedCache(A)[id].ready <=>
          \E e \in A : e.kind = "data" /\ e.value.id = id
    BY InterpretedCacheReadyIffRequestOccurred
<1> QED BY SMT, <1>1, <1>4, <1>5
=============================================================================
