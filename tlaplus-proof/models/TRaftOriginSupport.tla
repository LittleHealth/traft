-------------------------- MODULE TRaftOriginSupport ------------------------
EXTENDS TRaftBoundaryProof
USE ParameterAssumptions DEF ParameterAssumptions

HasAnchor(L, R) == L = {} \/
    \E p \in R : p.epoch = LastTerm(L) /\ Result(p) \subseteq L
FormalAnchors(F, R) == \A r \in Replicas : HasAnchor(F[r], R[r])
ReportAnchors(M) == \A m \in M :
    /\ \A p \in m.pending : p.epoch <= m.epoch
    /\ HasAnchor(m.entries, m.pending)
CanonicalAnchors(C, P) == \A t \in Terms :
    C[t] # {} => \E p \in P : p.epoch = t

THEOREM OriginFactsDecompose ==
    RecoveryOriginFacts <=>
       (FormalAnchors(formal, retained) /\ ReportAnchors(reportMessages)
        /\ CanonicalAnchors(canonical, proposals))
BY SMT DEF RecoveryOriginFacts, FormalAnchors, HasAnchor, ReportAnchors, CanonicalAnchors

THEOREM AnchorRetainedBySuperset ==
    ASSUME NEW L, NEW R, NEW S, HasAnchor(L, R), R \subseteq S
    PROVE HasAnchor(L, S)
BY SMT DEF HasAnchor

THEOREM CanonicalAnchorForAlignedLog ==
    ASSUME NEW L, NEW R, NEW C, NEW Ps, NEW t \in Nat,
           L # {}, L \subseteq Entries, IsFiniteSet(L),
           L \subseteq C[LastTerm(L)],
           \A e \in C[LastTerm(L)] : e.term <= LastTerm(L),
           \A e \in L : e.term <= t,
           \E q \in Ps : q.epoch = LastTerm(L) /\ Result(q) \subseteq L,
           R \subseteq Ps,
           \A p \in Ps : p.first.term = p.epoch,
           \A p, q \in Ps : p.epoch = q.epoch => p = q,
           \E p \in R : p.epoch = t /\ p.first \in L
    PROVE HasAnchor(L, R)
<1>1. PICK p \in R : p.epoch = t /\ p.first \in L
    OBVIOUS
<1>2. PICK q \in Ps : q.epoch = LastTerm(L) /\ Result(q) \subseteq L
    OBVIOUS
<1>3. \E e \in L : e.term = LastTerm(L)
    BY NonemptyLogLastTermIsRepresented
<1>4. LastTerm(L) \in Nat /\ LastTerm(L) <= t
    BY SMT, <1>3 DEF Entries, Terms
<1>5. t <= LastTerm(L)
    BY SMT, <1>1
<1>6. p = q
    BY SMT, <1>1, <1>2, <1>4, <1>5
<1> QED BY <1>1, <1>2, <1>6 DEF HasAnchor

THEOREM PostAlignmentSuppliesAnchor ==
    ASSUME RecoveryInvariant', FiniteLogInvariant',
           NEW r \in Replicas, Aligned(r, term[r])'
    PROVE HasAnchor(formal'[r], retained'[r])
<1>1. formal'[r] # {} /\ formal'[r] \subseteq Entries
      /\ IsFiniteSet(formal'[r]) /\ retained'[r] \subseteq proposals'
      /\ term'[r] \in Nat
    BY SMT DEF RecoveryInvariant, TypeOK, FiniteLogInvariant,
       FiniteNodeData, Aligned, Terms
<1>2. formal'[r] \subseteq canonical'[LastTerm(formal'[r])]
      /\ LastTerm(formal'[r]) \in Terms
      /\ \E q \in proposals' : q.epoch = LastTerm(formal'[r])
                  /\ Result(q) \subseteq formal'[r]
    BY SMT, <1>1 DEF RecoveryInvariant, CanonicalShape, Sublog
<1>3. (\A e \in canonical'[LastTerm(formal'[r])] : e.term <= LastTerm(formal'[r]))
      /\ (\A e \in formal'[r] : e.term <= term'[r])
      /\ (\A p, q \in proposals' : p.epoch = q.epoch => p = q)
      /\ (\A p \in proposals' : p.first.term = p.epoch)
      /\ (\E p \in retained'[r] : p.epoch = term'[r] /\ p.first \in formal'[r])
    <2>1. \A t \in Terms : \A e \in canonical'[t] : e.term <= t
        BY DEF RecoveryInvariant, CanonicalShape
    <2>2. (\A e \in formal'[r] : e.term <= term'[r])
          /\ (\A p, q \in proposals' : p.epoch = q.epoch => p = q)
        BY DEF RecoveryInvariant, CanonicalShape
    <2>3. \A p \in proposals' : p.first.term = p.epoch
        BY DEF RecoveryInvariant, TypeOK
    <2>4. \E p \in retained'[r] : p.epoch = term'[r] /\ p.first \in formal'[r]
        BY DEF Aligned
    <2> QED BY ONLY SMT, <1>2, <2>1, <2>2, <2>3, <2>4
<1> QED BY CanonicalAnchorForAlignedLog, <1>1, <1>2, <1>3

THEOREM ChangedNodeWithAlignmentKeepsFormalAnchors ==
    ASSUME FormalAnchors(formal, retained), RecoveryInvariant', FiniteLogInvariant',
           NEW r \in Replicas, Aligned(r, term[r])',
           \A s \in Replicas \ {r} : formal'[s] = formal[s] /\ retained[s] \subseteq retained'[s]
    PROVE FormalAnchors(formal', retained')
<1>1. HasAnchor(formal'[r], retained'[r])
    BY PostAlignmentSuppliesAnchor
<1>2. \A s \in Replicas \ {r} : HasAnchor(formal'[s], retained'[s])
    BY SMT, AnchorRetainedBySuperset DEF FormalAnchors
<1> QED BY SMT, <1>1, <1>2 DEF FormalAnchors

THEOREM UnchangedFormalGrowingRetainedKeepsAnchors ==
    ASSUME FormalAnchors(formal, retained), UNCHANGED formal,
           \A r \in Replicas : retained[r] \subseteq retained'[r]
    PROVE FormalAnchors(formal', retained')
BY SMT, AnchorRetainedBySuperset DEF FormalAnchors
=============================================================================
