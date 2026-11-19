------------------------- MODULE TRaftFiniteEntryOrder -----------------------
EXTENDS TRaftEntryOrderState, TRaftFiniteLogProof, SequenceTheorems

THEOREM EmptyEntryOrder ==
    Enumerates(<<>>, {}) /\ IncreasingEntryOrder(<<>>) /\ Len(<<>>) = Cardinality({})
BY SMT, EmptySeq, FS_EmptySet DEF Enumerates, SequenceEntries, IncreasingEntryOrder

THEOREM AppendEnumeratesOneNewElement ==
    ASSUME NEW S, NEW order, Enumerates(order, S), NEW e, e \notin S
    PROVE Enumerates(Append(order, e), S \cup {e})
<1>1. order \in Seq(S \cup {e}) /\ Len(order) \in Nat
      /\ SequenceEntries(order) = S
      /\ \A i, j \in 1..Len(order) : order[i] = order[j] => i = j
    BY SeqMonotonic, LenProperties DEF Enumerates
<1>2. Append(order, e) \in Seq(S \cup {e})
      /\ Len(Append(order, e)) = Len(order) + 1
      /\ (\A i \in 1..Len(order) : Append(order, e)[i] = order[i])
      /\ Append(order, e)[Len(order) + 1] = e
    BY AppendProperties, <1>1
<1>3. \A i \in 1..Len(order) : order[i] \in S /\ order[i] # e
    BY <1>1 DEF SequenceEntries
<1>4. SequenceEntries(Append(order, e)) = S \cup {e}
    BY SMT, <1>1, <1>2 DEF SequenceEntries
<1>5. \A i, j \in 1..Len(Append(order, e)) :
          Append(order, e)[i] = Append(order, e)[j] => i = j
    BY SMT, <1>1, <1>2, <1>3
<1> QED BY <1>2, <1>4, <1>5 DEF Enumerates

THEOREM AppendGreatestEntryKeepsOrder ==
    ASSUME NEW S, NEW order, Enumerates(order, S), IncreasingEntryOrder(order),
           NEW e, \A x \in S : x.index < e.index
    PROVE IncreasingEntryOrder(Append(order, e))
<1>1. order \in Seq(S \cup {e}) /\ Len(order) \in Nat
      /\ \A i \in 1..Len(order) : order[i] \in S
    BY SeqMonotonic, LenProperties DEF Enumerates, SequenceEntries
<1>2. Len(Append(order, e)) = Len(order) + 1
      /\ (\A i \in 1..Len(order) : Append(order, e)[i] = order[i])
      /\ Append(order, e)[Len(order) + 1] = e
    BY AppendProperties, <1>1
<1> QED BY SMT, <1>1, <1>2 DEF IncreasingEntryOrder

THEOREM FiniteCoherentEntriesHaveIncreasingOrder ==
    ASSUME NEW S, IsFiniteSet(S), S \subseteq Entries, Coherent(S)
    PROVE \E order : Enumerates(order, S) /\ IncreasingEntryOrder(order)
                    /\ Len(order) = Cardinality(S)
<1>1. DEFINE P(T) == \E order : Enumerates(order, T) /\ IncreasingEntryOrder(order)
                                /\ Len(order) = Cardinality(T)
<1>2. ASSUME NEW T \in SUBSET S, \A U \in (SUBSET T) \ {T} : P(U)
      PROVE P(T)
    <2>1. IsFiniteSet(T) /\ T \subseteq Entries /\ Coherent(T)
        BY SMT, FS_Subset DEF Coherent
    <2>2. CASE T = {}
        BY EmptyEntryOrder, <2>2 DEF P
    <2>3. CASE T # {}
        <3>1. PICK e \in T : e.index = LastIndex(T)
            BY FiniteLogFrontier, <2>1, <2>3
        <3>2. \A x \in T \ {e} : x.index < e.index
            BY SMT, FiniteLogFrontier, <2>1, <3>1 DEF Coherent, Entries, Indices
        <3>30. T \ {e} \in (SUBSET T) \ {T} /\ (T \ {e}) \cup {e} = T
            BY SMT, <3>1
        <3>310. IsFiniteSet(T)
            BY <2>1
        <3>311. IsFiniteSet(T \ {e}) /\ Cardinality(T \ {e}) =
                    IF e \in T THEN Cardinality(T) - 1 ELSE Cardinality(T)
            BY ONLY FS_RemoveElement, <3>310, IsaM("blast")
        <3>312. Cardinality(T) \in Nat
            BY ONLY SMT, FS_CardinalityType, <3>310
        <3>31. IsFiniteSet(T \ {e}) /\ Cardinality(T \ {e}) = Cardinality(T) - 1
               /\ Cardinality(T) \in Nat
            BY ONLY SMT, <3>311, <3>312
        <3>3. T \ {e} \in (SUBSET T) \ {T}
              /\ IsFiniteSet(T \ {e}) /\ (T \ {e}) \cup {e} = T
              /\ Cardinality(T) = Cardinality(T \ {e}) + 1
            BY ONLY SMT, <3>30, <3>31
        <3>4. PICK order : Enumerates(order, T \ {e}) /\ IncreasingEntryOrder(order)
                          /\ Len(order) = Cardinality(T \ {e})
            BY <1>2, <3>3 DEF P
        <3>5. Enumerates(Append(order, e), T) /\ IncreasingEntryOrder(Append(order, e))
            BY AppendEnumeratesOneNewElement, AppendGreatestEntryKeepsOrder,
               <3>2, <3>3, <3>4
        <3>6. order \in Seq(T)
            BY SeqMonotonic, <3>4 DEF Enumerates
        <3>7. Len(Append(order, e)) = Len(order) + 1
            BY AppendProperties, <3>1, <3>6
        <3>8. Len(Append(order, e)) = Cardinality(T)
            BY ONLY SMT, <3>3, <3>4, <3>7
        <3> QED BY ONLY ZenonT(5), <3>5, <3>8 DEF P
    <2> QED BY <2>2, <2>3
<1>3. IsFiniteSet(S)
    OBVIOUS
<1> HIDE DEF P
<1>4. P(S)
    BY ONLY FS_WFInduction, <1>2, <1>3, IsaM("blast")
<1> QED BY <1>4 DEF P

THEOREM SortedEntryOrderExists ==
    ASSUME NEW S, IsFiniteSet(S), S \subseteq Entries, Coherent(S)
    PROVE SortedEntryOrder(S) \in EntryOrders(S)
<1>1. PICK order : Enumerates(order, S) /\ IncreasingEntryOrder(order)
                  /\ Len(order) = Cardinality(S)
    BY FiniteCoherentEntriesHaveIncreasingOrder
<1>2. order \in [1..Cardinality(S) -> S]
    BY LenProperties, <1>1 DEF Enumerates
<1>3. order \in EntryOrders(S)
    BY <1>1, <1>2 DEF EntryOrders
<1> QED BY ZenonT(5), <1>3 DEF SortedEntryOrder
=============================================================================
