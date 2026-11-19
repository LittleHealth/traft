-------------------------- MODULE TRaftSequenceFold --------------------------
EXTENDS Naturals, Sequences

\* Primitive recursive function, not a recursive operator. The function is
\* total over Nat; values after the finite input ends remain unchanged.
FoldTrace(order, initial, Step(_, _)) ==
    LET trace[n \in Nat] ==
          IF n = 0 THEN initial
          ELSE IF n <= Len(order) THEN Step(trace[n - 1], order[n]) ELSE trace[n - 1]
    IN trace
Fold(order, initial, Step(_, _)) == FoldTrace(order, initial, Step)[Len(order)]
=============================================================================
