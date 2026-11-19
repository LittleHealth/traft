----------------------- MODULE TRaftFiniteRequestOrder -----------------------
EXTENDS TRaftClientLinearizationState, SequenceTheorems, FiniteSetTheorems,
        FunctionTheorems, TLAPS

THEOREM FiniteSetHasAnEnumeratingOrder ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE FiniteOrders(S) # {}
<1>1. Cardinality(S) \in Nat /\ ExistsBijection(1..Cardinality(S), S)
    BY FS_CardinalityType
<1>2. PICK order \in Bijection(1..Cardinality(S), S) : TRUE
    BY <1>1 DEF ExistsBijection
<1>3. order \in [1..Cardinality(S) -> S]
      /\ (\A i, j \in 1..Cardinality(S) : order[i] = order[j] => i = j)
      /\ order \in Surjection(1..Cardinality(S), S)
    BY Fun_BijectionProperties, <1>2
<1>4. order \in Seq(S)
    <2>1. Seq(S) = (UNION {[1..n -> S] : n \in Nat})
        BY ONLY SeqDef
    <2>2. [1..Cardinality(S) -> S] \in {[1..n -> S] : n \in Nat}
        BY ONLY <1>1
    <2> QED BY ONLY <1>3, <2>1, <2>2
<1>5. Len(order) \in Nat /\ DOMAIN order = 1..Len(order)
      /\ DOMAIN order = 1..Cardinality(S)
    BY LenProperties, <1>3, <1>4
<1>6. Len(order) = Cardinality(S)
    BY ONLY SMT, <1>1, <1>5
<1>7. \A x \in S : \E i \in 1..Cardinality(S) : order[i] = x
    BY Fun_SurjectionProperties, <1>3
<1>8. Enumerates(order, S)
    BY <1>3, <1>4, <1>6, <1>7 DEF Enumerates, SequenceEntries
<1>9. order \in FiniteOrders(S)
    BY <1>3, <1>8 DEF FiniteOrders
<1> QED BY <1>9

THEOREM EnumeratingOrderHasCardinalLength ==
    ASSUME NEW S, IsFiniteSet(S), NEW order, Enumerates(order, S)
    PROVE Len(order) = Cardinality(S) /\ order \in FiniteOrders(S)
<1>1. order \in Seq(S) /\ order \in [1..Len(order) -> S]
      /\ Len(order) \in Nat /\ SequenceEntries(order) = S
      /\ \A i, j \in 1..Len(order) : order[i] = order[j] => i = j
    BY LenProperties DEF Enumerates
<1>2. \A x \in S : \E i \in 1..Len(order) : order[i] = x
    BY <1>1 DEF SequenceEntries
<1>3. order \in Bijection(1..Len(order), S)
    BY Fun_IsBij, <1>1, <1>2
<1>4. ExistsBijection(1..Len(order), S)
    BY <1>3 DEF ExistsBijection
<1>5. Cardinality(1..Len(order)) = Len(order) /\ IsFiniteSet(1..Len(order))
    BY SMT, FS_Interval, <1>1
<1>6. Cardinality(1..Len(order)) = Cardinality(S)
    BY FS_Bijection, <1>4, <1>5
<1> QED BY <1>1, <1>5, <1>6 DEF FiniteOrders
=============================================================================
