-------------------------- MODULE TRaftFiniteLogProof ------------------------
EXTENDS TRaftCore, FiniteSetTheorems, TLAPS
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM FiniteNaturalsHaveMaximum ==
    ASSUME NEW S, IsFiniteSet(S), S \subseteq Nat, S # {}
    PROVE \E m \in S : \A x \in S : x <= m
<1>1. DEFINE P(T) == T \subseteq Nat =>
                       (T = {} \/ \E m \in T : \A x \in T : x <= m)
<1>2. P({})
    BY SMT DEF P
<1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T
      PROVE P(T \cup {x})
    <2>1. SUFFICES ASSUME T \cup {x} \subseteq Nat
                  PROVE \E m \in T \cup {x} : \A y \in T \cup {x} : y <= m
        BY SMT DEF P
    <2>2. x \in Nat /\ T \subseteq Nat
        BY SMT, <2>1
    <2>3. CASE T = {}
        BY SMT, <2>2, <2>3
    <2>4. CASE T # {}
        <3>1. PICK m \in T : \A y \in T : y <= m
            BY ONLY ZenonT(5), <1>3, <2>2, <2>4 DEF P
        <3>2. m \in Nat
            BY SMT, <2>2, <3>1
        <3>3. CASE x <= m
            BY SMT, <3>1, <3>3
        <3>4. CASE x > m
            BY SMT, <2>2, <3>1, <3>2, <3>4
        <3> QED BY SMT, <2>2, <3>2, <3>3, <3>4
    <2> QED BY <2>3, <2>4
<1>35. IsFiniteSet(S)
    OBVIOUS
<1> HIDE DEF P
<1>4. P(S)
    BY ONLY FS_Induction, <1>2, <1>3, <1>35, IsaM("blast")
<1> QED BY <1>4 DEF P

THEOREM MaxOrChoosesMaximum ==
    ASSUME NEW S, NEW empty, IsFiniteSet(S), S \subseteq Nat, S # {}
    PROVE MaxOr(S, empty) \in S /\ \A x \in S : x <= MaxOr(S, empty)
<1>1. \E m \in S : \A x \in S : x <= m
    BY FiniteNaturalsHaveMaximum
<1> QED BY ZenonT(5), <1>1 DEF MaxOr

THEOREM FinitePartitionCount ==
    ASSUME NEW L, IsFiniteSet(L), NEW p
    PROVE IsFiniteSet(Part(L, p)) /\ Count(L, p) \in Nat
<1>1. Part(L, p) \subseteq L
    BY SMT DEF Part
<1>2. IsFiniteSet(Part(L, p))
    BY SMT, <1>1, FS_Subset
<1> QED BY SMT, <1>2, FS_CardinalityType DEF Count

THEOREM SubsetAndCountCompletePartition ==
    ASSUME NEW L, NEW F, NEW p, IsFiniteSet(L), F \subseteq L,
           Count(F, p) = Count(L, p)
    PROVE Part(F, p) = Part(L, p)
<1>1. F \subseteq L /\ IsFiniteSet(L)
    OBVIOUS
<1>2. Part(F, p) \subseteq Part(L, p)
    BY ONLY SMT, <1>1 DEF Part
<1>3. IsFiniteSet(Part(L, p))
    BY ONLY FinitePartitionCount, <1>1
<1> QED BY SMT, <1>2, <1>3, FS_Subset DEF Count


THEOREM EmptyLogFrontier ==
    Cur({}) = -1 /\ LastIndex({}) = 0 /\ \A p : Count({}, p) = 0
BY SMT, FS_EmptySet DEF Cur, LastIndex, MaxOr, Count, Part

THEOREM FiniteLogFrontier ==
    ASSUME NEW L, IsFiniteSet(L), L \subseteq Entries, L # {}
    PROVE /\ Cur(L) \in Nat /\ LastIndex(L) \in Nat
          /\ \A e \in L : e.part <= Cur(L) /\ e.index <= LastIndex(L)
          /\ \E e \in L : e.part = Cur(L)
          /\ \E e \in L : e.index = LastIndex(L)
<1>0. IsFiniteSet(L)
    OBVIOUS
<1>1. IsFiniteSet({e.part : e \in L})
    BY ONLY <1>0, FS_Image, IsaM("blast")
<1>2. IsFiniteSet({e.index : e \in L})
    BY ONLY <1>0, FS_Image, IsaM("blast")
<1>3. {e.part : e \in L} \subseteq Nat /\ {e.part : e \in L} # {}
      /\ {e.index : e \in L} \subseteq Nat /\ {e.index : e \in L} # {}
    BY SMT DEF Entries, Partitions, Indices
<1>4. Cur(L) \in {e.part : e \in L}
      /\ \A x \in {e.part : e \in L} : x <= Cur(L)
    BY MaxOrChoosesMaximum, <1>1, <1>3 DEF Cur
<1>5. LastIndex(L) \in {e.index : e \in L}
      /\ \A x \in {e.index : e \in L} : x <= LastIndex(L)
    BY MaxOrChoosesMaximum, <1>2, <1>3 DEF LastIndex
<1> QED BY SMT, <1>3, <1>4, <1>5

THEOREM CoherentNewPartition ==
    ASSUME NEW L, L \subseteq Entries, Coherent(L), NEW e \in Entries,
           \A x \in L : x.index < e.index /\ x.part < e.part,
           (e.kind = "noop") <=> (e.value = NoValue)
    PROVE Coherent(L \cup {e})
BY SMT DEF Coherent, Entries, Indices, Partitions

THEOREM CoherentOpenPartitionExtension ==
    ASSUME NEW L, L \subseteq Entries, Coherent(L), NEW e \in Entries,
           \A x \in L : x.index < e.index /\ x.part <= e.part,
           \A x \in L : x.part = e.part => x.term = e.term,
           (e.kind = "noop") <=> (e.value = NoValue)
    PROVE Coherent(L \cup {e})
BY SMT DEF Coherent, Entries, Indices, Partitions

THEOREM CountUnchangedOutsidePartition ==
    ASSUME NEW L, NEW e, NEW p, e.part # p
    PROVE Part(L \cup {e}, p) = Part(L, p)
          /\ Count(L \cup {e}, p) = Count(L, p)
BY SMT DEF Part, Count
=============================================================================
