----------------------- MODULE TRaftCertifiedSourceState ---------------------
EXTENDS TRaftClosedHistoryState

\* Pending recovery proposals are deliberately not an installed-log source.
CertifiedLogEntries(V, P) ==
    (UNION {v.entries : v \in V}) \cup (UNION {Result(p) : p \in P})
FormalEntriesFrom(F, V, P) == \A r \in Replicas : F[r] \subseteq CertifiedLogEntries(V, P)
InstalledEntriesHaveSource == FormalEntriesFrom(formal, leaderViews, confirmations)
CertifiedContexts(E, V, P) == {ctx \in E : ctx.entry \in CertifiedLogEntries(V, P)}
CertifiedPartitionHistory ==
    /\ ClosedPartitionOrigins(partitionHistory, CertifiedContexts(entryContexts, leaderViews, confirmations))
    /\ ClosedPartitionOrigins(appliedPartitionHistory, CertifiedContexts(entryContexts, leaderViews, confirmations))
=============================================================================
