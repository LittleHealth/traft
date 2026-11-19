------------------------ MODULE TRaftHistoryFactsProof -----------------------
EXTENDS TRaftHistoryProjectionProof, TRaftElectionTemporal

THEOREM CanonicalViewLinksInitially == ProofInit => CanonicalViewLinks
BY SMT DEF ProofInit, Init, CanonicalViewLinks

THEOREM CanonicalViewLinksStep ==
    ASSUME CanonicalViewLinks, ElectionInvariant', Observe, GhostNext
    PROVE CanonicalViewLinks'
<1>1. \A t \in Terms : canonical[t] \subseteq canonical'[t]
    BY SMT DEF GhostNext
<1>2. \A r \in Replicas : role'[r] = "Leader" =>
          term'[r] \in Terms /\ formal'[r] \subseteq canonical'[term'[r]]
    <2>1. ASSUME NEW r \in Replicas, role'[r] = "Leader"
          PROVE term'[r] \in Terms /\ formal'[r] \subseteq canonical'[term'[r]]
        <3>1. term'[r] \in Terms
            BY <2>1 DEF ElectionInvariant, ElectionTypes
        <3>2. formal'[r] \subseteq (UNION {formal'[n] : n \in {s \in Replicas :
                              role'[s] = "Leader" /\ term'[s] = term'[r]}})
            BY ONLY SMT, <2>1
        <3>3. GhostNext
            OBVIOUS
        <3> QED BY ONLY SMT, <3>1, <3>2, <3>3 DEF GhostNext
    <2> QED BY <2>1
<1>3. \A v \in leaderViews : v.epoch \in Terms /\ v.entries \subseteq canonical'[v.epoch]
    BY SMT, <1>1 DEF CanonicalViewLinks
<1> QED BY SMT, <1>2, <1>3 DEF CanonicalViewLinks, Observe

THEOREM CanonicalViewLinksStuttering ==
    ASSUME CanonicalViewLinks, UNCHANGED proofVars
    PROVE CanonicalViewLinks'
BY SMT DEF CanonicalViewLinks, proofVars, vars, protocolVars, observerVars

THEOREM CanonicalViewLinksAlways == ProofSpec => []CanonicalViewLinks
<1>1. ProofSpec => []ElectionInvariant
    BY PTL, ProofSpecificationProjects, ElectionInvariantAlways
<1>2. ProofInit => CanonicalViewLinks
    BY CanonicalViewLinksInitially
<1>3. CanonicalViewLinks /\ ElectionInvariant' /\ [ProofNext]_proofVars => CanonicalViewLinks'
    BY SMT, CanonicalViewLinksStep, CanonicalViewLinksStuttering DEF ProofNext, Next
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ProofSpec

THEOREM OffersBelongToCanonicalLog ==
    ASSUME OfferProvenance, CanonicalViewLinks
    PROVE \A o \in offers : o.epoch \in Terms /\ o.entry \in canonical[o.epoch]
BY SMT DEF OfferProvenance, CanonicalViewLinks
=============================================================================
