---------------------- MODULE TRaftContextOriginState ------------------------
EXTENDS TRaftCore

ContextOrigins(C, E) == \A ctx \in E :
    ctx.entry.term \in Terms /\ ctx.entry \in C[ctx.entry.term]
=============================================================================
