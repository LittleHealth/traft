--------------------- MODULE TRaftHistoryProjectionProof ---------------------
EXTENDS TRaftProofState, TLAPS

THEOREM ProofSpecificationProjects == ProofSpec => Spec
<1>1. ProofInit => Init
    BY DEF ProofInit
<1>2. [ProofNext]_proofVars => [Next]_vars
    BY SMT DEF ProofNext, proofVars
<1> QED BY PTL, <1>1, <1>2 DEF ProofSpec, Spec
=============================================================================
