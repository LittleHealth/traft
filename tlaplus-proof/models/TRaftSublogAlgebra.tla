-------------------------- MODULE TRaftSublogAlgebra -------------------------
EXTENDS TRaftLogContextState, TRaftBoundaryCountSupport, TRaftCanonicalPrefixProof

SublogIn(L, C, P) == L = {} \/
    LET t == LastTerm(L)
    IN /\ t \in Terms /\ L \subseteq C[t]
       /\ \E p \in P : p.epoch = t /\ Result(p) \subseteq L
       /\ Prefix(L, Cur(L) - 1) = Prefix(C[t], Cur(L) - 1)

THEOREM GreatestElementDeterminesMaxOr ==
    ASSUME NEW S, S \subseteq Int, NEW m \in S, \A x \in S : x <= m, NEW empty
    PROVE MaxOr(S, empty) = m
<1>1. S # {} /\ \E x \in S : \A y \in S : y <= x
    BY SMT
<1>2. MaxOr(S, empty) \in S /\ \A y \in S : y <= MaxOr(S, empty)
    BY ZenonT(5), <1>1 DEF MaxOr
<1>3. m \in Int /\ MaxOr(S, empty) \in Int
      /\ m <= MaxOr(S, empty) /\ MaxOr(S, empty) <= m
    BY ZenonT(5), <1>2
<1> QED BY ONLY SMT, <1>3

THEOREM NewGreatestEntryDeterminesLastTerm ==
    ASSUME NEW L, L \subseteq Entries, NEW e \in Entries,
           \A x \in L : x.index < e.index
    PROVE LastIndex(L \cup {e}) = e.index /\ LastTerm(L \cup {e}) = e.term
<1>0. e.index \in Nat /\ \A x \in L : x.index \in Nat /\ x.index < e.index
    BY SMT DEF Entries, Indices
<1>1. {x.index : x \in L \cup {e}} \subseteq Int
      /\ e.index \in {x.index : x \in L \cup {e}}
      /\ \A n \in {x.index : x \in L \cup {e}} : n <= e.index
    BY SMT DEF Entries, Indices
<1>2. LastIndex(L \cup {e}) = e.index
    BY GreatestElementDeterminesMaxOr, <1>1 DEF LastIndex
<1>3. \A x \in L \cup {e} : x.index = e.index => x = e
    BY ONLY SMT, <1>0
<1>4. (CHOOSE x \in L \cup {e} : x.index = LastIndex(L \cup {e})) = e
    BY ZenonT(5), <1>2, <1>3
<1> QED BY ONLY ZenonT(5), <1>2, <1>4 DEF LastTerm

THEOREM GreatestPartitionDeterminesCur ==
    ASSUME NEW L, L \subseteq Entries, NEW e \in L,
           \A x \in L : x.part <= e.part
    PROVE Cur(L) = e.part
<1>1. {x.part : x \in L} \subseteq Int /\ e.part \in {x.part : x \in L}
      /\ \A n \in {x.part : x \in L} : n <= e.part
    BY SMT DEF Entries, Partitions
<1> QED BY GreatestElementDeterminesMaxOr, <1>1 DEF Cur

THEOREM SublogTransport ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L), NEW C, NEW D, NEW P, NEW Q,
           SublogIn(L, C, P), P \subseteq Q,
           \A t \in Terms : C[t] \subseteq D[t], CanonicalPrefixesPersist(C, D)
    PROVE SublogIn(L, D, Q)
<1>1. CASE L = {}
    BY <1>1 DEF SublogIn
<1>2. CASE L # {}
    <2>1. LastTerm(L) \in Terms /\ L \subseteq C[LastTerm(L)]
          /\ (\E p \in P : p.epoch = LastTerm(L) /\ Result(p) \subseteq L)
          /\ Prefix(L, Cur(L) - 1) = Prefix(C[LastTerm(L)], Cur(L) - 1)
        BY <1>2 DEF SublogIn
    <2>2. PICK e \in L : e.part = Cur(L)
        BY FiniteLogFrontier, <1>2
    <2>3. Prefix(D[LastTerm(L)], Cur(L) - 1) = Prefix(C[LastTerm(L)], Cur(L) - 1)
        BY <2>1, <2>2 DEF CanonicalPrefixesPersist
    <2> QED BY SMT, <2>1, <2>3 DEF SublogIn
<1> QED BY <1>1, <1>2

THEOREM SublogInheritsCanonicalContexts ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L), NEW C, NEW P, NEW E,
           C \in [Terms -> SUBSET Entries], SublogIn(L, C, P), CanonicalContexts(C, E)
    PROVE LogContexts(L, E)
<1>1. CASE L = {}
    BY <1>1 DEF LogContexts
<1>2. CASE L # {}
    <2>1. LastTerm(L) \in Terms /\ L \subseteq C[LastTerm(L)]
          /\ Prefix(L, Cur(L) - 1) = Prefix(C[LastTerm(L)], Cur(L) - 1)
        BY <1>2 DEF SublogIn
    <2>2. Cur(L) \in Int /\ \A x \in L : x.part \in Int /\ x.part <= Cur(L)
        BY FiniteLogPartitionFrontier
    <2>20. \A x \in C[LastTerm(L)] : x.part \in Int
        BY SMT, <2>1 DEF Entries, Partitions
    <2>3. \A e \in L : Prefix(L, e.part - 1) = Prefix(C[LastTerm(L)], e.part - 1)
        BY SMT, <2>1, <2>2, <2>20 DEF Prefix
    <2>4. LogContexts(C[LastTerm(L)], E)
        BY <2>1 DEF CanonicalContexts
    <2>5. ASSUME NEW e \in L
          PROVE \E ctx \in E : ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
        <3>1. e \in C[LastTerm(L)] /\ Prefix(L, e.part - 1) = Prefix(C[LastTerm(L)], e.part - 1)
            BY <2>1, <2>3, <2>5
        <3> QED BY ONLY SMT, <2>4, <3>1 DEF LogContexts
    <2> QED BY <2>5 DEF LogContexts
<1> QED BY <1>1, <1>2

=============================================================================
