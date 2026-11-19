-------------------- MODULE TRaftCanonicalDefinitionProof -------------------
EXTENDS TRaftHistoryRefinementProof

THEOREM CanonicalDefinitionInitially == ProofInit => CanonicalDefinition
<1>0. SUFFICES ASSUME ProofInit PROVE CanonicalDefinition
    OBVIOUS
<1>1. Init /\ canonical = [t \in Terms |-> {}]
    BY <1>0 DEF ProofInit, GhostInit
<1>2. DerivedCanonical = [t \in Terms |-> {}]
    BY CoreInitializationLifts, <1>1 DEF LiftedInit
<1> QED BY <1>1, <1>2 DEF CanonicalDefinition

THEOREM CanonicalDefinitionStep ==
    ASSUME CanonicalDefinition, ProofNext
    PROVE CanonicalDefinition'
<1>1. Next /\ GhostNext
    BY DEF ProofNext
<1>2. LiftedNext(DerivedCanonical)
    BY CoreNextLifts, <1>1
<1>3. canonical = DerivedCanonical
    BY DEF CanonicalDefinition
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3
    DEF CanonicalDefinition, GhostNext, LiftedNext, ProposedAt

THEOREM CanonicalDefinitionStuttering ==
    ASSUME CanonicalDefinition, UNCHANGED proofVars
    PROVE CanonicalDefinition'
<1>1. UNCHANGED vars /\ UNCHANGED canonical
    BY DEF proofVars
<1>2. UNCHANGED DerivedCanonical
    BY CoreStutteringLifts, <1>1 DEF LiftedVars
<1> QED BY <1>1, <1>2 DEF CanonicalDefinition

THEOREM CanonicalDefinitionAlways == ProofSpec => []CanonicalDefinition
<1>1. ProofInit => CanonicalDefinition
    BY CanonicalDefinitionInitially
<1>2. CanonicalDefinition /\ [ProofNext]_proofVars => CanonicalDefinition'
    BY CanonicalDefinitionStep, CanonicalDefinitionStuttering
<1> QED BY PTL, <1>1, <1>2 DEF ProofSpec
=============================================================================
