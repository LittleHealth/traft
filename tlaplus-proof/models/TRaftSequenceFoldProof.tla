----------------------- MODULE TRaftSequenceFoldProof ------------------------
EXTENDS TRaftSequenceFold, SequenceTheorems, TLAPS

\* Qualify this instance: SequenceTheorems also has a LOCAL instance.
NI == INSTANCE NaturalsInduction

THEOREM FoldTraceEquation ==
    ASSUME NEW order, NEW initial, NEW Step(_, _)
    PROVE FoldTrace(order, initial, Step) = [n \in Nat |->
              IF n = 0 THEN initial
              ELSE IF n <= Len(order) THEN Step(FoldTrace(order, initial, Step)[n - 1], order[n])
                   ELSE FoldTrace(order, initial, Step)[n - 1]]
<1>1. DEFINE D(previous, n) == IF n <= Len(order) THEN Step(previous, order[n]) ELSE previous
<1>2. NI!NatInductiveDefHypothesis(FoldTrace(order, initial, Step), initial, D)
    BY DEF FoldTrace, NI!NatInductiveDefHypothesis, D
<1> HIDE DEF D
<1>3. NI!NatInductiveDefConclusion(FoldTrace(order, initial, Step), initial, D)
    BY ONLY NI!NatInductiveDef, <1>2, IsaM("blast")
<1> QED BY <1>3 DEF NI!NatInductiveDefConclusion, D

THEOREM FoldTraceStartsAtInitial ==
    ASSUME NEW order, NEW initial, NEW Step(_, _)
    PROVE FoldTrace(order, initial, Step)[0] = initial
<1>1. FoldTrace(order, initial, Step) = [n \in Nat |->
              IF n = 0 THEN initial
              ELSE IF n <= Len(order) THEN Step(FoldTrace(order, initial, Step)[n - 1], order[n])
                   ELSE FoldTrace(order, initial, Step)[n - 1]]
    BY FoldTraceEquation
<1> QED BY ONLY SMT, <1>1

THEOREM FoldTraceAdvances ==
    ASSUME NEW S, NEW order \in Seq(S), NEW initial, NEW Step(_, _),
           NEW n \in 1..Len(order)
    PROVE FoldTrace(order, initial, Step)[n] = Step(FoldTrace(order, initial, Step)[n - 1], order[n])
<1>1. Len(order) \in Nat
    BY LenProperties
<1>2. n \in Nat /\ n # 0 /\ n <= Len(order)
    BY SMT, <1>1
<1>3. FoldTrace(order, initial, Step) = [i \in Nat |->
              IF i = 0 THEN initial
              ELSE IF i <= Len(order) THEN Step(FoldTrace(order, initial, Step)[i - 1], order[i])
                   ELSE FoldTrace(order, initial, Step)[i - 1]]
    BY FoldTraceEquation
<1> QED BY ONLY ZenonT(5), <1>2, <1>3

THEOREM FoldTraceIsTyped ==
    ASSUME NEW S, NEW T, NEW order \in Seq(S), NEW initial \in T, NEW Step(_, _),
           \A state \in T, element \in S : Step(state, element) \in T
    PROVE FoldTrace(order, initial, Step) \in [Nat -> T]
<1>1. DEFINE D(previous, n) == IF n <= Len(order) THEN Step(previous, order[n]) ELSE previous
<1>2. NI!NatInductiveDefConclusion(FoldTrace(order, initial, Step), initial, D)
    BY FoldTraceEquation DEF NI!NatInductiveDefConclusion, D
<1>3. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>4. \A previous \in T, n \in Nat \ {0} : D(previous, n) \in T
    BY SMT, <1>3 DEF D
<1>5. initial \in T
    OBVIOUS
<1> HIDE DEF D
<1> QED BY ONLY NI!NatInductiveDefType, <1>2, <1>4, <1>5, IsaM("blast")

THEOREM FoldPrefixesAgree ==
    ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW initial, NEW Step(_, _),
           NEW k \in Nat, k <= Len(a), k <= Len(b),
           \A i \in 1..k : a[i] = b[i]
    PROVE /\ \A i \in 0..k : FoldTrace(a, initial, Step)[i] = FoldTrace(b, initial, Step)[i]
          /\ FoldTrace(a, initial, Step)[k] = FoldTrace(b, initial, Step)[k]
<1>1. DEFINE P(i) == i <= k => FoldTrace(a, initial, Step)[i] = FoldTrace(b, initial, Step)[i]
<1>2. P(0)
    BY FoldTraceStartsAtInitial DEF P
<1>3. ASSUME NEW i \in Nat, P(i)
      PROVE P(i + 1)
    <2>1. SUFFICES ASSUME i + 1 <= k
                  PROVE FoldTrace(a, initial, Step)[i + 1] = FoldTrace(b, initial, Step)[i + 1]
        BY DEF P
    <2>2. Len(a) \in Nat /\ Len(b) \in Nat
        BY LenProperties
    <2>3. i + 1 \in 1..Len(a) /\ i + 1 \in 1..Len(b) /\ i + 1 \in 1..k
          /\ i <= k /\ (i + 1) - 1 = i
        BY SMT, <1>3, <2>1, <2>2
    <2>4. FoldTrace(a, initial, Step)[i] = FoldTrace(b, initial, Step)[i]
          /\ a[i + 1] = b[i + 1]
        BY <1>3, <2>3 DEF P
    <2>5. FoldTrace(a, initial, Step)[i + 1] = Step(FoldTrace(a, initial, Step)[i], a[i + 1])
          /\ FoldTrace(b, initial, Step)[i + 1] = Step(FoldTrace(b, initial, Step)[i], b[i + 1])
        BY FoldTraceAdvances, <2>3
    <2> QED BY ONLY <2>4, <2>5
<1> HIDE DEF P
<1>4. \A i \in Nat : P(i)
    BY ONLY NI!NatInduction, <1>2, <1>3, IsaM("blast")
<1> QED BY SMT, <1>4 DEF P

THEOREM FoldAppend ==
    ASSUME NEW S, NEW order \in Seq(S), NEW element \in S, NEW initial, NEW Step(_, _)
    PROVE Fold(Append(order, element), initial, Step) = Step(Fold(order, initial, Step), element)
<1>0. order \in Seq(S)
    OBVIOUS
<1>1. Len(order) \in Nat
      /\ Append(order, element) \in Seq(S) /\ Len(Append(order, element)) = Len(order) + 1
      /\ (\A i \in 1..Len(order) : Append(order, element)[i] = order[i])
      /\ Append(order, element)[Len(order) + 1] = element
    BY LenProperties, AppendProperties
<1>10. Len(order) <= Len(Append(order, element)) /\ Len(order) <= Len(order)
      /\ Len(order) \in 0..Len(order)
    BY ONLY SMT, <1>1
<1>2. FoldTrace(Append(order, element), initial, Step)[Len(order)] = FoldTrace(order, initial, Step)[Len(order)]
    <2>1. DEFINE P(n) == n <= Len(order) =>
              FoldTrace(Append(order, element), initial, Step)[n] = FoldTrace(order, initial, Step)[n]
    <2>2. P(0)
        BY FoldTraceStartsAtInitial DEF P
    <2>3. ASSUME NEW n \in Nat, P(n)
          PROVE P(n + 1)
        <3>1. SUFFICES ASSUME n + 1 <= Len(order)
                      PROVE FoldTrace(Append(order, element), initial, Step)[n + 1]
                           = FoldTrace(order, initial, Step)[n + 1]
            BY DEF P
        <3>2. n <= Len(order) /\ n + 1 \in 1..Len(order)
              /\ n + 1 \in 1..Len(Append(order, element)) /\ (n + 1) - 1 = n
            BY ONLY SMT, <1>1, <2>3, <3>1
        <3>3. FoldTrace(Append(order, element), initial, Step)[n]
                 = FoldTrace(order, initial, Step)[n]
              /\ Append(order, element)[n + 1] = order[n + 1]
            BY <1>1, <2>3, <3>2 DEF P
        <3>40. FoldTrace(Append(order, element), initial, Step)[n + 1]
                 = Step(FoldTrace(Append(order, element), initial, Step)[(n + 1) - 1], Append(order, element)[n + 1])
            BY ONLY FoldTraceAdvances, <1>1, <3>2, IsaM("blast")
        <3>41. FoldTrace(order, initial, Step)[n + 1]
                 = Step(FoldTrace(order, initial, Step)[(n + 1) - 1], order[n + 1])
            BY ONLY FoldTraceAdvances, <1>0, <3>2, IsaM("blast")
        <3>4. FoldTrace(Append(order, element), initial, Step)[n + 1]
                 = Step(FoldTrace(Append(order, element), initial, Step)[n], Append(order, element)[n + 1])
              /\ FoldTrace(order, initial, Step)[n + 1]
                 = Step(FoldTrace(order, initial, Step)[n], order[n + 1])
            BY ONLY <3>2, <3>40, <3>41
        <3> QED BY ONLY <3>3, <3>4
    <2> HIDE DEF P
    <2>4. \A n \in Nat : P(n)
        BY ONLY NI!NatInduction, <2>2, <2>3, IsaM("blast")
    <2> QED BY <1>1, <2>4 DEF P
<1>3. Len(order) + 1 \in 1..Len(Append(order, element)) /\ (Len(order) + 1) - 1 = Len(order)
    BY ONLY SMT, <1>1
<1>40. FoldTrace(Append(order, element), initial, Step)[Len(order) + 1]
         = Step(FoldTrace(Append(order, element), initial, Step)[(Len(order) + 1) - 1],
                Append(order, element)[Len(order) + 1])
    BY ONLY FoldTraceAdvances, <1>1, <1>3, IsaM("blast")
<1>4. FoldTrace(Append(order, element), initial, Step)[Len(order) + 1]
         = Step(FoldTrace(Append(order, element), initial, Step)[Len(order)], element)
    BY ONLY <1>1, <1>3, <1>40
<1> QED BY ONLY <1>1, <1>2, <1>4 DEF Fold
=============================================================================
