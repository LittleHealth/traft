--------------------- MODULE ProofRecursiveOperatorProbe ---------------------
EXTENDS Naturals, TLAPS
RECURSIVE CountDown(_)
CountDown(n) == IF n = 0 THEN 0 ELSE CountDown(n - 1) + 1
THEOREM RecursiveOperatorZero == CountDown(0) = 0
BY DEF CountDown
=============================================================================
