-------------------------- MODULE TRaftLogContextState -----------------------
EXTENDS TRaftCore

LogContexts(L, E) == \A e \in L : \E ctx \in E :
    ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
CanonicalContexts(C, E) == \A t \in Terms : LogContexts(C[t], E)
=============================================================================
