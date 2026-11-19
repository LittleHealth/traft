------------------- MODULE TRaftLogMatchingFromInvariant ---------------------
EXTENDS TRaftContextOriginProof, TRaftBoundaryProof

THEOREM PartitionHasCanonicalPrefix ==
    ASSUME ContextOrigins(canonical, entryContexts), CanonicalShape,
           EntryContextUnique, NEW L, ContextSound(L), NEW p, Part(L, p) # {}
    PROVE Origin(L, p) \in Terms
          /\ Prefix(L, p - 1) = Prefix(canonical[Origin(L, p)], p - 1)
<1>1. DEFINE e == CHOOSE x \in Part(L, p) : TRUE
<1>2. e \in Part(L, p)
    BY ZenonT(5) DEF e
<1>3. e \in L /\ e.part = p /\ e.term = Origin(L, p)
    BY SMT, <1>2 DEF Part, Origin, e
<1>40. ContextSound(L)
    OBVIOUS
<1>4. PICK ctx \in entryContexts : ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
    BY ONLY ZenonT(5), <1>3, <1>40 DEF ContextSound
<1>5. ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
    BY ContextOriginIdentifiesCanonicalPrefix, <1>4
<1>6. ctx.entry.term \in Terms
    BY <1>4 DEF ContextOrigins
<1> QED BY ONLY SMT, <1>3, <1>4, <1>5, <1>6

THEOREM ContextOriginsImplyLogMatching ==
    (ContextOrigins(canonical, entryContexts) /\ CanonicalShape /\ EntryContextUnique) => LogMatching
<1>1. ASSUME ContextOrigins(canonical, entryContexts), CanonicalShape, EntryContextUnique,
            NEW r \in Replicas, NEW s \in Replicas, NEW p \in Partitions,
            Part(formal[r], p) # {}, Part(formal[s], p) # {},
            Origin(formal[r], p) = Origin(formal[s], p)
      PROVE Prefix(formal[r], p - 1) = Prefix(formal[s], p - 1)
    <2>1. ContextSound(formal[r]) /\ ContextSound(formal[s])
        BY <1>1 DEF CanonicalShape
    <2>2. Prefix(formal[r], p - 1) = Prefix(canonical[Origin(formal[r], p)], p - 1)
          /\ Prefix(formal[s], p - 1) = Prefix(canonical[Origin(formal[s], p)], p - 1)
        BY PartitionHasCanonicalPrefix, <1>1, <2>1
    <2> QED BY <1>1, <2>2
<1> QED BY <1>1 DEF LogMatching

THEOREM LastIndexBelongsToOpenPartition ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L), L # {}, Coherent(L)
    PROVE LastTerm(L) = Origin(L, Cur(L))
<1>1. DEFINE e == CHOOSE x \in L : x.index = LastIndex(L)
<1>2. \E x \in L : x.index = LastIndex(L)
    BY FiniteLogFrontier
<1>3. e \in L /\ e.index = LastIndex(L)
    BY ZenonT(5), <1>2 DEF e
<1>4. PICK f \in L : f.part = Cur(L)
    BY FiniteLogFrontier
<1>5. f.index <= e.index /\ e.part <= Cur(L)
      /\ f.index \in Nat /\ e.index \in Nat /\ e.part \in Nat /\ f.part \in Nat
    BY SMT, FiniteLogFrontier, <1>3, <1>4 DEF Entries, Indices, Partitions
<1>6. e.part = Cur(L)
    BY SMT, <1>3, <1>4, <1>5 DEF Coherent
<1>7. Part(L, Cur(L)) # {}
    BY SMT, <1>3, <1>6 DEF Part
<1>8. (CHOOSE x \in Part(L, Cur(L)) : TRUE) \in Part(L, Cur(L))
    BY ZenonT(5), <1>7
<1> QED BY SMT, <1>3, <1>6, <1>7, <1>8 DEF LastTerm, Origin, Coherent, Part, e

THEOREM LogMatchingImpliesRankEquivalence ==
    (ProofInvariant /\ LogMatching) => IntraPartitionRankEquivalence
<1>1. ASSUME ProofInvariant, LogMatching, NEW r \in Replicas, NEW s \in Replicas,
            Cur(formal[r]) >= 0, Cur(formal[r]) = Cur(formal[s]),
            Origin(formal[r], Cur(formal[r])) = Origin(formal[s], Cur(formal[s])),
            Count(formal[r], Cur(formal[r])) = Count(formal[s], Cur(formal[s]))
      PROVE ClosedPrefix(formal[r]) = ClosedPrefix(formal[s]) /\ Rank(formal[r]) = Rank(formal[s])
    <2>1. formal[r] \subseteq Entries /\ formal[s] \subseteq Entries
          /\ IsFiniteSet(formal[r]) /\ IsFiniteSet(formal[s])
          /\ Coherent(formal[r]) /\ Coherent(formal[s])
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
           TypeOK, FiniteLogInvariant, FiniteNodeData
    <2>2. formal[r] # {} /\ formal[s] # {}
        BY SMT, EmptyLogFrontier, <1>1
    <2>3. LastTerm(formal[r]) = Origin(formal[r], Cur(formal[r]))
          /\ LastTerm(formal[s]) = Origin(formal[s], Cur(formal[s]))
        BY LastIndexBelongsToOpenPartition, <2>1, <2>2
    <2>4. Cur(formal[r]) \in Partitions
          /\ Part(formal[r], Cur(formal[r])) # {} /\ Part(formal[s], Cur(formal[r])) # {}
        BY SMT, FiniteLogFrontier, <1>1, <2>1, <2>2 DEF Entries, Part
    <2>5. Prefix(formal[r], Cur(formal[r]) - 1) = Prefix(formal[s], Cur(formal[r]) - 1)
        BY SMT, <1>1, <2>4 DEF LogMatching
    <2> QED BY SMT, <1>1, <2>3, <2>5 DEF ClosedPrefix, Rank
<1> QED BY <1>1 DEF IntraPartitionRankEquivalence
=============================================================================
