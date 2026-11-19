-------------------------- MODULE ProofToolNegative --------------------------
EXTENDS Naturals, TLAPS
\* Intentional invalid arithmetic theorem. The runner MUST report failure.
\* Isabelle also has positive controls in the shared-import selftest.
THEOREM Invalid == 1 = 2
BY IsaM("auto")
=============================================================================
