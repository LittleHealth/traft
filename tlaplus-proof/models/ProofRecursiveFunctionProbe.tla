--------------------- MODULE ProofRecursiveFunctionProbe ---------------------
EXTENDS Naturals, TLAPS
CountDown[n \in Nat] == IF n = 0 THEN 0 ELSE CountDown[n - 1] + 1
THEOREM CountDownHasSolution ==
    \E f : f = [n \in Nat |-> IF n = 0 THEN 0 ELSE f[n - 1] + 1]
<1>1. DEFINE f == [n \in Nat |-> n]
<1>2. f = [n \in Nat |-> IF n = 0 THEN 0 ELSE f[n - 1] + 1]
    BY SMT DEF f
<1> QED BY <1>2
THEOREM RecursiveFunctionZero == CountDown[0] = 0
<1>1. CountDown = [n \in Nat |-> IF n = 0 THEN 0 ELSE CountDown[n - 1] + 1]
    BY ZenonT(5), CountDownHasSolution DEF CountDown
<1> QED BY SMT, <1>1
=============================================================================
