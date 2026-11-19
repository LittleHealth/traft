----------------------- MODULE TRaftClosedHistoryState -----------------------
EXTENDS TRaftCore

HasClosedContext(E, p, S) == \E ctx \in E :
    ctx.entry.part > p /\ Part(ctx.prefix, p) = S
ClosedPartitionOrigins(H, E) == \A h \in H : HasClosedContext(E, h.part, h.entries)
HistoryPartitionCompleteness ==
    /\ ClosedPartitionOrigins(partitionHistory, entryContexts)
    /\ ClosedPartitionOrigins(appliedPartitionHistory, entryContexts)
=============================================================================
