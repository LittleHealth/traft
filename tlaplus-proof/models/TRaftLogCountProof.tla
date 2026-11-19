--------------------------- MODULE TRaftLogCountProof ------------------------
EXTENDS TRaftFiniteLogProof, TRaftBoundaryCountSupport

BoundedLogCounts(L) == \A p \in Partitions : Count(L, p) <= MaxPartitionSize
CanonicalLogShape(C) ==
    /\ C \in [Terms -> SUBSET Entries]
    /\ \A t \in Terms : Coherent(C[t]) /\ BoundedLogCounts(C[t])
                           /\ \A e \in C[t] : e.term <= t

THEOREM CountAfterSingleAppend ==
    ASSUME NEW L, IsFiniteSet(L), NEW e, e \notin L, NEW p
    PROVE Count(L \cup {e}, p) = Count(L, p) + (IF e.part = p THEN 1 ELSE 0)
<1>1. IsFiniteSet(Part(L, p)) /\ Count(L, p) \in Nat
    BY FinitePartitionCount
<1>2. e \notin Part(L, p)
    BY SMT DEF Part
<1>3. CASE e.part = p
    <2>1. Part(L \cup {e}, p) = Part(L, p) \cup {e}
        BY ONLY SMT, <1>3 DEF Part
    <2>2. Cardinality(Part(L, p) \cup {e}) = Cardinality(Part(L, p)) + 1
        BY ONLY SMT, FS_AddElement, <1>1, <1>2
    <2> QED BY ONLY SMT, <1>3, <2>1, <2>2 DEF Count
<1>4. CASE e.part # p
    <2>1. Count(L \cup {e}, p) = Count(L, p)
        BY CountUnchangedOutsidePartition, <1>4
    <2> QED BY ONLY SMT, <1>1, <1>4, <2>1
<1> QED BY <1>3, <1>4

THEOREM AppendKeepsCountBound ==
    ASSUME NEW L, IsFiniteSet(L), BoundedLogCounts(L), NEW e,
           e.part \in Partitions, e \notin L, Count(L, e.part) < MaxPartitionSize
    PROVE BoundedLogCounts(L \cup {e})
<1>0. MaxPartitionSize \in Nat
    BY ParameterAssumptions DEF ParameterAssumptions
<1>1. \A p \in Partitions : Count(L \cup {e}, p) = Count(L, p) + (IF e.part = p THEN 1 ELSE 0)
    BY CountAfterSingleAppend
<1>2. \A p \in Partitions : Count(L, p) \in Nat
    BY FinitePartitionCount
<1>3. ASSUME NEW p \in Partitions
      PROVE Count(L \cup {e}, p) <= MaxPartitionSize
    <2>1. Count(L, p) \in Nat /\ Count(L, p) <= MaxPartitionSize
          /\ Count(L, e.part) < MaxPartitionSize
          /\ Count(L \cup {e}, p) = Count(L, p) + (IF e.part = p THEN 1 ELSE 0)
        BY <1>1, <1>2, <1>3 DEF BoundedLogCounts
    <2> QED BY ONLY SMT, <1>0, <2>1
<1> QED BY <1>3 DEF BoundedLogCounts

THEOREM NewPartitionIsEmpty ==
    ASSUME NEW L, IsFiniteSet(L), L \subseteq Entries, NEW p, p = Cur(L) + 1
    PROVE Count(L, p) = 0
<1>0. p = Cur(L) + 1
    OBVIOUS
<1>1. Cur(L) \in Int /\ \A e \in L : e.part \in Int /\ e.part <= Cur(L)
    BY FiniteLogPartitionFrontier
<1>2. Part(L, p) = {}
    BY ONLY SMT, <1>0, <1>1 DEF Part
<1> QED BY ONLY FS_EmptySet, <1>2 DEF Count

THEOREM ReplaceCanonicalLogShape ==
    ASSUME NEW C, CanonicalLogShape(C), NEW t \in Terms, NEW L,
           L \subseteq Entries, Coherent(L), BoundedLogCounts(L),
           \A e \in L : e.term <= t,
           NEW D, D = [u \in Terms |-> IF u = t THEN L ELSE C[u]]
    PROVE CanonicalLogShape(D)
BY SMT DEF CanonicalLogShape
=============================================================================
