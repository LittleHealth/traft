------------------------- MODULE TRaftFoldSimulation ------------------------
EXTENDS TRaftSequenceFoldProof

THEOREM FoldPreservesIndexedRelation ==
    ASSUME NEW S, NEW order \in Seq(S), NEW a, NEW b,
           NEW F(_, _), NEW G(_, _), NEW R(_, _, _),
           R(0, a, b),
           \A n \in 0..(Len(order) - 1) : \A x, y :
             R(n, x, y) => R(n + 1, F(x, order[n + 1]), G(y, order[n + 1]))
    PROVE R(Len(order), Fold(order, a, F), Fold(order, b, G))
<1>1. Len(order) \in Nat
    BY LenProperties
<1>2. DEFINE P(n) == n <= Len(order) =>
          R(n, FoldTrace(order, a, F)[n], FoldTrace(order, b, G)[n])
<1>3. P(0)
    BY FoldTraceStartsAtInitial DEF P
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE P(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE R(n + 1, FoldTrace(order, a, F)[n + 1], FoldTrace(order, b, G)[n + 1])
        BY DEF P
    <2>2. n \in 0..(Len(order) - 1) /\ n <= Len(order)
          /\ n + 1 \in 1..Len(order) /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. R(n, FoldTrace(order, a, F)[n], FoldTrace(order, b, G)[n])
        BY <1>4, <2>2 DEF P
    <2>4. FoldTrace(order, a, F)[n + 1] = F(FoldTrace(order, a, F)[n], order[n + 1])
          /\ FoldTrace(order, b, G)[n + 1] = G(FoldTrace(order, b, G)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>5. \A n \in Nat : P(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF P, Fold

THEOREM FoldPreservesRelation ==
    ASSUME NEW S, NEW order \in Seq(S), NEW a, NEW b,
           NEW F(_, _), NEW G(_, _), NEW R(_, _), R(a, b),
           \A x, y : \A e \in S : R(x, y) => R(F(x, e), G(y, e))
    PROVE R(Fold(order, a, F), Fold(order, b, G))
<1>1. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>2. DEFINE P(n) == n <= Len(order) =>
          R(FoldTrace(order, a, F)[n], FoldTrace(order, b, G)[n])
<1>3. P(0)
    BY FoldTraceStartsAtInitial DEF P
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE P(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE R(FoldTrace(order, a, F)[n + 1], FoldTrace(order, b, G)[n + 1])
        BY DEF P
    <2>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
          /\ order[n + 1] \in S /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. R(FoldTrace(order, a, F)[n], FoldTrace(order, b, G)[n])
        BY <1>4, <2>2 DEF P
    <2>4. FoldTrace(order, a, F)[n + 1] = F(FoldTrace(order, a, F)[n], order[n + 1])
          /\ FoldTrace(order, b, G)[n + 1] = G(FoldTrace(order, b, G)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>5. \A n \in Nat : P(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF P, Fold

THEOREM FoldPreservesStatePredicate ==
    ASSUME NEW S, NEW order \in Seq(S), NEW initial, NEW Step(_, _),
           NEW P(_), P(initial), \A x : \A e \in S : P(x) => P(Step(x, e))
    PROVE P(Fold(order, initial, Step))
<1>1. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>2. DEFINE K(n) == n <= Len(order) => P(FoldTrace(order, initial, Step)[n])
<1>3. K(0)
    BY FoldTraceStartsAtInitial DEF K
<1>4. ASSUME NEW n \in Nat, K(n)
      PROVE K(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE P(FoldTrace(order, initial, Step)[n + 1])
        BY DEF K
    <2>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
          /\ order[n + 1] \in S /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. P(FoldTrace(order, initial, Step)[n])
        BY <1>4, <2>2 DEF K
    <2>4. FoldTrace(order, initial, Step)[n + 1]
              = Step(FoldTrace(order, initial, Step)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <2>2, <2>3, <2>4
<1> HIDE DEF K
<1>5. \A n \in Nat : K(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF K, Fold

THEOREM FoldStepsAgreeOnClosedStates ==
    ASSUME NEW S, NEW order \in Seq(S), NEW T, NEW initial \in T,
           NEW F(_, _), NEW G(_, _),
           \A x \in T, e \in S : F(x, e) \in T /\ F(x, e) = G(x, e)
    PROVE Fold(order, initial, F) = Fold(order, initial, G)
<1>1. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>2. DEFINE P(n) == n <= Len(order) =>
          (FoldTrace(order, initial, F)[n] \in T
           /\ FoldTrace(order, initial, F)[n] = FoldTrace(order, initial, G)[n])
<1>3. P(0)
    BY FoldTraceStartsAtInitial DEF P
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE P(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE FoldTrace(order, initial, F)[n + 1] \in T
                     /\ FoldTrace(order, initial, F)[n + 1] = FoldTrace(order, initial, G)[n + 1]
        BY DEF P
    <2>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
          /\ order[n + 1] \in S /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. FoldTrace(order, initial, F)[n] \in T
          /\ FoldTrace(order, initial, F)[n] = FoldTrace(order, initial, G)[n]
        BY <1>4, <2>2 DEF P
    <2>4. FoldTrace(order, initial, F)[n + 1] = F(FoldTrace(order, initial, F)[n], order[n + 1])
          /\ FoldTrace(order, initial, G)[n + 1] = G(FoldTrace(order, initial, G)[n], order[n + 1])
        BY FoldTraceAdvances, <2>2
    <2> QED BY <2>2, <2>3, <2>4
<1> HIDE DEF P
<1>5. \A n \in Nat : P(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF P, Fold
=============================================================================
