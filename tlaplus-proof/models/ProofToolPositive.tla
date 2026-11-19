-------------------------- MODULE ProofToolPositive --------------------------
EXTENDS Naturals, TLAPS
THEOREM Arithmetic == \A a, b \in Nat : a < b => a + 1 <= b
BY SMT
THEOREM Sets == \A A, B : A \subseteq B => A \cap B = A
BY SMT
=============================================================================
