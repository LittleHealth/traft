-------------------------- MODULE TRaftBoundaryProof ------------------------
EXTENDS TRaftProofState, TRaftFiniteLogProof
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM PrefixAtBoundary ==
    ASSUME NEW L, NEW p \in Int,
           \A e \in L : e.part \in Int
    PROVE Prefix(L, p) = Prefix(L, p - 1) \cup Part(L, p)
BY SMT DEF Prefix, Part

\* Quantity equality is useful only after the common-prefix and subset
\* premises have been established. No unconditional count equality rule.
THEOREM EqualCountCompletesCommonPrefix ==
    ASSUME NEW L, NEW F, NEW p \in Int,
           L \subseteq Entries, IsFiniteSet(L), F \subseteq L,
           Prefix(F, p - 1) = Prefix(L, p - 1),
           Count(F, p) = Count(L, p)
    PROVE Prefix(F, p) = Prefix(L, p)
<1>1. Part(F, p) = Part(L, p)
    BY SubsetAndCountCompletePartition
<1>2. (\A e \in F : e.part \in Int) /\ (\A e \in L : e.part \in Int)
    BY SMT DEF Entries, Partitions
<1>3. Prefix(F, p) = Prefix(F, p - 1) \cup Part(F, p)
      /\ Prefix(L, p) = Prefix(L, p - 1) \cup Part(L, p)
    BY PrefixAtBoundary, <1>2
<1> QED BY <1>1, <1>3

THEOREM ContextCountsTransferToLog ==
    ASSUME EntryBoundaryCounts, NEW L, L \subseteq Entries, ContextSound(L),
           NEW e \in L
    PROVE e.prevSize = Count(L, e.part - 1)
<1>1. PICK ctx \in entryContexts :
          ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
    BY SMT DEF ContextSound
<1>20. e.part - 1 \in Int
    BY SMT DEF Entries, Partitions
<1>21. Part(Prefix(L, e.part - 1), e.part - 1) = Part(L, e.part - 1)
    BY ONLY SMT, <1>20 DEF Part, Prefix
<1>2. Count(Prefix(L, e.part - 1), e.part - 1) = Count(L, e.part - 1)
    BY ONLY <1>21 DEF Count
<1> QED BY <1>1, <1>2 DEF EntryBoundaryCounts

THEOREM NonemptyLogLastTermIsRepresented ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L), L # {}
    PROVE \E e \in L : e.term = LastTerm(L)
<1>1. \E e \in L : e.index = LastIndex(L)
    BY FiniteLogFrontier
<1>2. (CHOOSE e \in L : e.index = LastIndex(L)) \in L
    BY ZenonT(5), <1>1
<1>3. LastTerm(L) = (CHOOSE e \in L : e.index = LastIndex(L)).term
    BY DEF LastTerm
<1> QED BY ONLY ZenonT(5), <1>2, <1>3

THEOREM AlignmentIdentifiesSublogEpoch ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW t \in Terms,
           term[r] = t, Aligned(r, t)
    PROVE formal[r] # {} /\ LastTerm(formal[r]) = t
<1>1. PICK p \in retained[r] : p.epoch = t /\ p.first \in formal[r]
    BY DEF Aligned
<1>2. formal[r] # {} /\ formal[r] \subseteq Entries
      /\ IsFiniteSet(formal[r]) /\ p \in proposals /\ p.first.term = t
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, TypeOK, FiniteLogInvariant, FiniteNodeData
<1>3. \E e \in formal[r] : e.term = LastTerm(formal[r])
    BY NonemptyLogLastTermIsRepresented, <1>2
<1>40. \A e \in formal[r] : e.term \in Nat /\ e.term <= t
    BY SMT DEF ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, CanonicalShape, TypeOK, Entries, Terms
<1>4. LastTerm(formal[r]) \in Nat /\ LastTerm(formal[r]) <= t
    BY ONLY SMT, <1>3, <1>40
<1>5. formal[r] \subseteq canonical[LastTerm(formal[r])]
      /\ LastTerm(formal[r]) \in Terms
    BY SMT, <1>2 DEF ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, CanonicalShape, Sublog
<1>60. \A u \in Terms : \A e \in canonical[u] : e.term <= u
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>61. p.first \in canonical[LastTerm(formal[r])]
    BY ONLY SMT, <1>1, <1>5
<1>6. t <= LastTerm(formal[r])
    BY ONLY SMT, <1>2, <1>5, <1>60, <1>61
<1> QED BY SMT, <1>2, <1>4, <1>6 DEF Terms

THEOREM NormalBoundaryUsesCompleteCommonPrefix ==
    ASSUME ProofInvariant, EntryContextUnique,
           NEW r \in Replicas, NEW o \in offers,
           NEW ctx \in entryContexts, CanReceive(r, o), ctx.entry = o.entry
    PROVE Prefix(formal[r], o.entry.part - 1) = ctx.prefix
<1>1. PICK v \in leaderViews :
          v.node = o.owner /\ v.epoch = o.epoch /\ o.entry \in v.entries
          /\ o.entry.term = o.epoch
    BY SMT DEF ProofInvariant, OfferProvenance
<1>2. o.epoch \in Terms /\ o.entry \in canonical[o.epoch]
    BY SMT, <1>1 DEF ProofInvariant, CanonicalViewLinks
<1>3. term[r] = o.epoch /\ Aligned(r, o.epoch)
    BY DEF CanReceive
<1>4. formal[r] # {} /\ LastTerm(formal[r]) = o.epoch
    BY AlignmentIdentifiesSublogEpoch, <1>2, <1>3
<1>5. formal[r] \subseteq canonical[o.epoch]
      /\ Prefix(formal[r], Cur(formal[r]) - 1) =
           Prefix(canonical[o.epoch], Cur(formal[r]) - 1)
      /\ ContextSound(canonical[o.epoch])
      /\ canonical[o.epoch] \subseteq Entries
      /\ IsFiniteSet(canonical[o.epoch])
    <2>1. CanonicalShape /\ CanonicalFinite
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. Sublog(formal[r])
        BY <2>1 DEF CanonicalShape
    <2>3. formal[r] \subseteq canonical[o.epoch]
          /\ Prefix(formal[r], Cur(formal[r]) - 1) =
               Prefix(canonical[o.epoch], Cur(formal[r]) - 1)
        BY ONLY SMT, <1>4, <2>2 DEF Sublog
    <2>4. ContextSound(canonical[o.epoch]) /\ canonical[o.epoch] \subseteq Entries
          /\ IsFiniteSet(canonical[o.epoch])
        BY ONLY SMT, <1>2, <2>1 DEF CanonicalShape, CanonicalFinite
    <2> QED BY <2>3, <2>4
<1>6. PICK source \in entryContexts : source.entry = o.entry
              /\ source.prefix = Prefix(canonical[o.epoch], o.entry.part - 1)
    BY SMT, <1>2, <1>5 DEF ContextSound
<1>7. ctx.prefix = Prefix(canonical[o.epoch], o.entry.part - 1)
    BY SMT, <1>6 DEF EntryContextUnique
<1>8. o.entry.prevSize = Count(canonical[o.epoch], o.entry.part - 1)
    BY ContextCountsTransferToLog, <1>2, <1>5 DEF ProofInvariant
<1>9. formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, FiniteLogInvariant, FiniteNodeData
<1>10. Cur(formal[r]) \in Nat
    BY FiniteLogFrontier, <1>4, <1>9
<1>11. CASE o.entry.part = Cur(formal[r])
    BY <1>5, <1>7, <1>11
<1>12. CASE o.entry.part # Cur(formal[r])
    <2>1. o.entry.part = Cur(formal[r]) + 1
          /\ Count(formal[r], Cur(formal[r])) = o.entry.prevSize
        BY <1>12 DEF CanReceive
    <2>2. Count(formal[r], Cur(formal[r])) = Count(canonical[o.epoch], Cur(formal[r]))
        BY SMT, <1>8, <1>10, <2>1
    <2>3. Prefix(formal[r], Cur(formal[r])) = Prefix(canonical[o.epoch], Cur(formal[r]))
        BY EqualCountCompletesCommonPrefix, <1>5, <1>10, <2>2
    <2> QED BY SMT, <1>7, <1>10, <2>1, <2>3
<1> QED BY <1>11, <1>12

THEOREM CountSafetyFromCandidate ==
    (ProofInvariant /\ EntryContextUnique) => NormalCountCheckSound
BY NormalBoundaryUsesCompleteCommonPrefix DEF NormalCountCheckSound
=============================================================================
