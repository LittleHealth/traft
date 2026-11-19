------------------------- MODULE TRaftSafetyObligations ----------------------
EXTENDS TRaftInitProof, TRaftInvariantStepProof, TRaftInvariantStutterProof

\* These derivations use exactly the same parameters and history variable.
\* EXTENDS shares their common definitions. Three named INSTANCE copies made
\* TLAPM 1.5 repeatedly compute levels in duplicated theorem contexts; no
\* substitution is needed here. Every imported theorem is audited separately.

\* Full safety is accepted only when every imported proof obligation is
\* separately checked from this source snapshot. A root success is insufficient.
THEOREM InitialInvariant == ProofInit => Inv
BY ONLY InitEstablishesInvariant DEF Inv

THEOREM ObservedProtocolInvariant == ProofSpec => []Inv
<1>1. Inv /\ [ProofNext]_proofVars => Inv'
    BY ONLY InductiveStep, StutteringPreservesInvariant
<1> QED BY ONLY PTL, InitialInvariant, <1>1 DEF ProofSpec

THEOREM ObservedProtocolSafety == ProofSpec => []Safety
BY ONLY PTL, ObservedProtocolInvariant DEF Inv
=============================================================================
