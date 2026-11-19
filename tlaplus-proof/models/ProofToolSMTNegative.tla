------------------------- MODULE ProofToolSMTNegative ------------------------
EXTENDS TLAPS
\* Separate SMT negative control: no infinite arithmetic model is required.
\* The arithmetic negative theorem is retained in ProofToolNegative.
THEOREM Invalid == FALSE
BY SMT
=============================================================================
