---------------------- MODULE TRaftRecoveryOriginInduction ------------------
EXTENDS TRaftInvariantDefinitions, TRaftOriginActions, TRaftHistoryRefinementProof
USE FormalFaultsDisabled DEF FormalFaultsDisabled

THEOREM GhostKeepsCanonicalAnchors ==
    ASSUME CanonicalAnchors(canonical, proposals),
           proposals \subseteq proposals', ControlInvariant', GhostNext
    PROVE CanonicalAnchors(canonical', proposals')
<1>1. ASSUME NEW t \in Terms, ~\E p \in proposals' : p.epoch = t
      PROVE canonical'[t] = {}
    <2>1. canonical[t] = {}
        BY SMT, <1>1 DEF CanonicalAnchors
    <2>2. {q \in proposals' : q.epoch = t} = {}
        BY SMT, <1>1
    <2>3. ~\E r \in Replicas : role'[r] = "Leader" /\ term'[r] = t
        BY SMT, <1>1 DEF ControlInvariant, ControlShape
    <2>4. {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t} = {}
        BY SMT, <2>3
    <2>5. canonical' = [u \in Terms |-> canonical[u] \cup
            (UNION {Result(p) : p \in {q \in proposals' : q.epoch = u}}) \cup
            (UNION {formal'[r] : r \in {s \in Replicas :
                              role'[s] = "Leader" /\ term'[s] = u}})]
        BY DEF GhostNext
    <2> QED BY ONLY SMT, <1>1, <2>1, <2>2, <2>4, <2>5
<1> QED BY <1>1 DEF CanonicalAnchors

\* This is one component of simultaneous induction. Its post-state premises
\* must be proved earlier by independent steps; none is assumed by Spec.
THEOREM RecoveryOriginInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant', FiniteLogInvariant', ControlInvariant'
    PROVE RecoveryOriginFacts'
<1>1. ProofInvariant /\ ProtocolNext /\ GhostNext
    BY DEF Inv, ProofNext, Next
<1>2. FormalAnchors(formal', retained')
    BY ProtocolKeepsFormalAnchors, <1>1
<1>3. ReportAnchors(reportMessages')
    BY ProtocolKeepsReportAnchors, <1>1
<1>4. CanonicalAnchors(canonical, proposals)
    BY SMT, OriginFactsDecompose DEF Inv, ProofInvariant, PreProvenanceInvariant
<1>5. proposals \subseteq proposals'
    BY ProposalsNeverShrink, <1>1
<1>6. CanonicalAnchors(canonical', proposals')
    BY GhostKeepsCanonicalAnchors, <1>4, <1>5, <1>1
<1> QED BY <1>2, <1>3, <1>6
    DEF RecoveryOriginFacts, FormalAnchors, ReportAnchors, CanonicalAnchors, HasAnchor
=============================================================================
