---------------------- MODULE TRaftCanonicalFiniteProof ----------------------
EXTENDS TRaftHistoryProjectionProof, TRaftFiniteTemporal
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM CanonicalInitiallyFinite == GhostInit => CanonicalFinite
BY SMT, FS_EmptySet DEF GhostInit, CanonicalFinite

THEOREM CanonicalFiniteStep ==
    ASSUME CanonicalFinite, FiniteLogInvariant', GhostNext
    PROVE CanonicalFinite'
<1>1. ASSUME NEW t \in Terms
      PROVE IsFiniteSet(canonical'[t])
    <2>1. IsFiniteSet({q \in proposals' : q.epoch = t})
        BY SMT, <1>1, FS_Subset DEF FiniteLogInvariant, FiniteChannels
    <2>2. \A p \in {q \in proposals' : q.epoch = t} : IsFiniteSet(Result(p))
        BY SMT, <1>1 DEF FiniteLogInvariant, FiniteProposals
    <2>3. IsFiniteSet(UNION {Result(p) : p \in {q \in proposals' : q.epoch = t}})
        BY ONLY <2>1, <2>2, FiniteImageUnion, IsaM("blast")
    <2>4. IsFiniteSet({s \in Replicas : role'[s] = "Leader" /\ term'[s] = t})
        BY SMT, FS_Subset
    <2>5. \A r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t} :
              IsFiniteSet(formal'[r])
        BY SMT, <1>1 DEF FiniteLogInvariant, FiniteNodeData
    <2>6. IsFiniteSet(UNION {formal'[r] : r \in {s \in Replicas :
                                      role'[s] = "Leader" /\ term'[s] = t}})
        BY ONLY <2>4, <2>5, FiniteImageUnion, IsaM("blast")
    <2>7. IsFiniteSet(canonical[t])
        BY <1>1 DEF CanonicalFinite
    <2>8. IsFiniteSet(canonical[t] \cup
                    (UNION {Result(p) : p \in {q \in proposals' : q.epoch = t}}))
        BY FiniteBinaryUnion, <2>3, <2>7
    <2> QED BY <1>1, <2>6, <2>8, FiniteBinaryUnion DEF GhostNext
<1> QED BY <1>1 DEF CanonicalFinite

THEOREM CanonicalFiniteAlways == ProofSpec => []CanonicalFinite
<1>1. ProofSpec => []FiniteLogInvariant
    BY PTL, ProofSpecificationProjects, FiniteLogInvariantAlways
<1>2. ProofInit => CanonicalFinite
    BY CanonicalInitiallyFinite DEF ProofInit
<1>3. CanonicalFinite /\ FiniteLogInvariant' /\ [ProofNext]_proofVars => CanonicalFinite'
    BY SMT, CanonicalFiniteStep DEF ProofNext, CanonicalFinite, proofVars
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ProofSpec
=============================================================================
