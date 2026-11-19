--------------------------- MODULE TRaftSublogSupport ------------------------
EXTENDS TRaftSublogAlgebra, TRaftCreatedEntryProof

THEOREM AnchoredCanonicalSubsetHasCurrentLastTerm ==
    ASSUME ProofInvariant, NEW p \in proposals, NEW L, IsFiniteSet(L),
           L \subseteq canonical[p.epoch], p.first \in L
    PROVE LastTerm(L) = p.epoch
<1>1. p.epoch \in Terms /\ L \subseteq Entries /\ p.first.term = p.epoch
      /\ p.first.index = LastIndex(p.prefix) + 1
      /\ p.prefix \subseteq Entries /\ IsFiniteSet(Result(p))
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       CanonicalShape, FiniteLogInvariant, FiniteProposals
<1>2. IsFiniteSet(p.prefix)
    BY SMT, FS_Subset, <1>1 DEF Result
<1>3. LastIndex(p.prefix) \in Nat
      /\ \A x \in p.prefix : x.index <= LastIndex(p.prefix) /\ x.index \in Nat
    BY FiniteLogNumericFrontier, <1>1, <1>2
<1>4. PICK x \in L : x.index = LastIndex(L)
    BY SMT, FiniteLogFrontier, <1>1
<1>5. p.first.index <= x.index /\ p.first.index \in Nat /\ x.index \in Nat
    BY SMT, FiniteLogFrontier, <1>1, <1>4 DEF Entries, Indices
<1>6. x \notin p.prefix
    BY ONLY SMT, <1>1, <1>3, <1>5
<1>7. \A e \in canonical[p.epoch] \ Result(p) : e.term = p.epoch
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>70. Coherent(canonical[p.epoch])
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>8. \A e \in L : e.index = LastIndex(L) => e = x
    BY SMT, <1>4, <1>70 DEF Coherent
<1>9. LastTerm(L) = x.term
    BY ZenonT(5), <1>4, <1>8 DEF LastTerm
<1> QED BY SMT, <1>1, <1>4, <1>6, <1>7, <1>9 DEF Result

THEOREM RecoveryResultIsCanonicalSublog ==
    ASSUME ProofInvariant, NEW p \in proposals
    PROVE SublogIn(Result(p), canonical, proposals)
<1>1. p.epoch \in Terms /\ p.prefix \subseteq Entries /\ p.first \in Entries
      /\ IsFiniteSet(Result(p)) /\ Result(p) \subseteq canonical[p.epoch]
      /\ p.first.part = Cur(p.prefix) + 1
      /\ Prefix(canonical[p.epoch], p.first.part - 1) = p.prefix
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       CanonicalShape, FiniteLogInvariant, FiniteProposals
<1>2. LastTerm(Result(p)) = p.epoch
    BY AnchoredCanonicalSubsetHasCurrentLastTerm, <1>1 DEF Result
<1>3. IsFiniteSet(p.prefix)
    BY SMT, FS_Subset, <1>1 DEF Result
<1>4. Cur(p.prefix) \in Int /\ \A x \in p.prefix : x.part \in Int /\ x.part <= Cur(p.prefix)
    BY FiniteLogPartitionFrontier, <1>1, <1>3
<1>5. Cur(Result(p)) = p.first.part
    BY SMT, GreatestPartitionDeterminesCur, <1>1, <1>4 DEF Result
<1>6. Prefix(Result(p), Cur(Result(p)) - 1) = p.prefix
    BY SMT, <1>1, <1>4, <1>5 DEF Result, Prefix
<1> QED BY SMT, <1>1, <1>2, <1>5, <1>6 DEF SublogIn
=============================================================================
