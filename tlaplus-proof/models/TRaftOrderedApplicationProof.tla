--------------------- MODULE TRaftOrderedApplicationProof --------------------
EXTENDS TRaftPointStoreStep, TRaftFiniteEntryOrder, TRaftSequenceFoldProof

PrefixEntrySet(order, n) == {order[i] : i \in 1..n}
PartitionOrdered(order) == \A i, j \in 1..Len(order) :
    i < j => order[i].part <= order[j].part

THEOREM FiniteSequencePrefixSet ==
    ASSUME NEW S, NEW order \in Seq(S), NEW n \in 0..Len(order)
    PROVE IsFiniteSet(PrefixEntrySet(order, n)) /\ PrefixEntrySet(order, n) \subseteq S
<1>1. Len(order) \in Nat /\ order \in [1..Len(order) -> S]
    BY LenProperties
<1>2. IsFiniteSet(1..n)
    BY SMT, FS_Interval, <1>1
<1>3. IsFiniteSet(PrefixEntrySet(order, n))
    BY ONLY FS_Image, <1>2, IsaM("blast") DEF PrefixEntrySet
<1> QED BY SMT, <1>1, <1>3 DEF PrefixEntrySet

THEOREM NextSequenceEntryExtendsPrefix ==
    ASSUME NEW S, NEW order, Enumerates(order, S), NEW n \in Nat, n < Len(order)
    PROVE /\ PrefixEntrySet(order, n + 1) = PrefixEntrySet(order, n) \cup {order[n + 1]}
          /\ order[n + 1] \in S \ PrefixEntrySet(order, n)
<1>1. order \in [1..Len(order) -> S] /\ Len(order) \in Nat
    BY LenProperties DEF Enumerates
<1> QED BY SMT, <1>1 DEF PrefixEntrySet, Enumerates

THEOREM OrderedFoldHasAppliedSetInterpretation ==
    ASSUME NEW A, IsFiniteSet(A), A \subseteq Entries,
           NEW S, S \subseteq Entries, A \cap S = {},
           NEW order, Enumerates(order, S), PartitionOrdered(order),
           PointLog(A \cup S), RequestIdentityState,
           \A e \in A \cup S : e.kind = "data" => e.value \in calls,
           \A a \in A, e \in S : a.part <= e.part
    PROVE Fold(order, AppliedPointState(A), EntryPointStep) = AppliedPointState(A \cup S)
<1>1. order \in Seq(S) /\ Len(order) \in Nat
      /\ PrefixEntrySet(order, Len(order)) = S
    BY LenProperties DEF Enumerates, PrefixEntrySet, SequenceEntries
<1>2. DEFINE P(n) == n <= Len(order) =>
          FoldTrace(order, AppliedPointState(A), EntryPointStep)[n]
            = AppliedPointState(A \cup PrefixEntrySet(order, n))
<1>3. P(0)
    <2>1. PrefixEntrySet(order, 0) = {} /\ A \cup {} = A
        BY ONLY SMT DEF PrefixEntrySet
    <2>2. FoldTrace(order, AppliedPointState(A), EntryPointStep)[0] = AppliedPointState(A)
        BY FoldTraceStartsAtInitial
    <2> QED BY <2>1, <2>2 DEF P
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE P(n + 1)
    <2>1. SUFFICES ASSUME n + 1 <= Len(order)
                  PROVE FoldTrace(order, AppliedPointState(A), EntryPointStep)[n + 1]
                     = AppliedPointState(A \cup PrefixEntrySet(order, n + 1))
        BY DEF P
    <2>2. n < Len(order) /\ n <= Len(order) /\ n \in 0..Len(order)
          /\ n + 1 \in 1..Len(order) /\ (n + 1) - 1 = n
        BY ONLY SMT, <1>1, <1>4, <2>1
    <2>3. IsFiniteSet(PrefixEntrySet(order, n)) /\ PrefixEntrySet(order, n) \subseteq S
          /\ PrefixEntrySet(order, n + 1) = PrefixEntrySet(order, n) \cup {order[n + 1]}
          /\ order[n + 1] \in S \ PrefixEntrySet(order, n)
        BY FiniteSequencePrefixSet, NextSequenceEntryExtendsPrefix, <1>1, <2>2
    <2>4. IsFiniteSet(A \cup PrefixEntrySet(order, n))
          /\ A \cup PrefixEntrySet(order, n) \subseteq Entries
          /\ order[n + 1] \in Entries \ (A \cup PrefixEntrySet(order, n))
          /\ PointLog((A \cup PrefixEntrySet(order, n)) \cup {order[n + 1]})
        <3>1. IsFiniteSet(A \cup PrefixEntrySet(order, n))
            BY FS_Union, <2>3
        <3>2. A \cup PrefixEntrySet(order, n) \subseteq Entries
              /\ order[n + 1] \in Entries \ (A \cup PrefixEntrySet(order, n))
              /\ (A \cup PrefixEntrySet(order, n)) \cup {order[n + 1]} \subseteq A \cup S
            BY <2>3
        <3>3. PointLog((A \cup PrefixEntrySet(order, n)) \cup {order[n + 1]})
            BY PointLogInheritedBySubset, <3>2
        <3> QED BY <3>1, <3>2, <3>3
    <2>5. \A x \in A \cup PrefixEntrySet(order, n) : x.part <= order[n + 1].part
        BY SMT, <1>1, <2>2, <2>3 DEF PartitionOrdered, PrefixEntrySet
    <2>6. AppliedPointState((A \cup PrefixEntrySet(order, n)) \cup {order[n + 1]})
            = EntryPointStep(AppliedPointState(A \cup PrefixEntrySet(order, n)), order[n + 1])
        BY OrderedSetExtensionIsPointStep, <2>3, <2>4, <2>5
    <2>7. FoldTrace(order, AppliedPointState(A), EntryPointStep)[n + 1]
            = EntryPointStep(FoldTrace(order, AppliedPointState(A), EntryPointStep)[n], order[n + 1])
        BY FoldTraceAdvances, <1>1, <2>2
    <2> QED BY <1>4, <2>2, <2>3, <2>6, <2>7 DEF P
<1> HIDE DEF P
<1>5. \A n \in Nat : P(n)
    BY ONLY NI!NatInduction, <1>3, <1>4, IsaM("blast")
<1> QED BY <1>1, <1>5 DEF P, Fold
=============================================================================
