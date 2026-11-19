-------------------------- MODULE TRaftFunctionProof -------------------------
EXTENDS TLAPS

THEOREM FunctionUpdatePreservesDomainShape ==
    ASSUME NEW N, NEW F, F = [r \in N |-> F[r]], NEW n \in N,
           NEW value, NEW G, G = [F EXCEPT ![n] = value]
    PROVE G = [r \in N |-> G[r]]
BY SMT

=============================================================================
