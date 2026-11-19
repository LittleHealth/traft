----------------------- MODULE TRaftCertifiedHistoryProof --------------------
EXTENDS TRaftCertifiedSourceProof, TRaftClosedHistoryProof

THEOREM CertifiedContextsGrow ==
    ASSUME NEW E, NEW F, NEW V, NEW W, NEW P, NEW Q,
           E \subseteq F, V \subseteq W, P \subseteq Q
    PROVE CertifiedContexts(E, V, P) \subseteq CertifiedContexts(F, W, Q)
BY SMT, CertifiedSourcesGrow DEF CertifiedContexts

THEOREM CertifiedFormalContexts ==
    ASSUME NEW L, NEW E, NEW V, NEW P,
           L \subseteq CertifiedLogEntries(V, P),
           \A e \in L : \E ctx \in E :
               ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
    PROVE \A e \in L : \E ctx \in CertifiedContexts(E, V, P) :
               ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
BY SMT DEF CertifiedContexts

THEOREM CertifiedHistoriesInitially == ProofInit => CertifiedPartitionHistory
BY SMT DEF ProofInit, Init, CertifiedPartitionHistory, ClosedPartitionOrigins

THEOREM CertifiedHistoriesInductiveStep ==
    ASSUME CertifiedPartitionHistory, RecoveryInvariant', FiniteLogInvariant',
           InstalledEntriesHaveSource', Next
    PROVE CertifiedPartitionHistory'
<1>1. entryContexts \subseteq entryContexts' /\ leaderViews \subseteq leaderViews'
          /\ confirmations \subseteq confirmations'
    BY SMT, ConfirmationsOnlyGrow DEF Next, Observe
<1>2. CertifiedContexts(entryContexts, leaderViews, confirmations) \subseteq
          CertifiedContexts(entryContexts', leaderViews', confirmations')
    BY CertifiedContextsGrow, <1>1
<1>3. \A h \in partitionHistory \cup appliedPartitionHistory :
          HasClosedContext(CertifiedContexts(entryContexts', leaderViews', confirmations'), h.part, h.entries)
    BY SMT, <1>2, ClosedContextSurvivesHistoryGrowth
       DEF CertifiedPartitionHistory, ClosedPartitionOrigins
<1>4. \A r \in Replicas : formal'[r] \subseteq Entries
          /\ IsFiniteSet(formal'[r]) /\ ContextSound(formal[r])'
          /\ formal'[r] \subseteq CertifiedLogEntries(leaderViews', confirmations')
    BY DEF RecoveryInvariant, TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData,
       InstalledEntriesHaveSource, FormalEntriesFrom
<1>50. \A r \in Replicas : \A e \in formal'[r] :
          \E ctx \in entryContexts' :
              ctx.entry = e /\ ctx.prefix = Prefix(formal'[r], e.part - 1)
    BY ONLY SMT, <1>4 DEF ContextSound
<1>5. \A r \in Replicas : \A e \in formal'[r] :
          \E ctx \in CertifiedContexts(entryContexts', leaderViews', confirmations') :
              ctx.entry = e /\ ctx.prefix = Prefix(formal'[r], e.part - 1)
    BY ONLY CertifiedFormalContexts, <1>4, <1>50
<1>6. \A r \in Replicas : Cur(formal'[r]) \in Int
    BY FiniteLogPartitionFrontier, <1>4
<1>7. \A r \in Replicas : \A p \in Int :
          (p < Cur(formal'[r]) /\ Part(formal'[r], p) # {}) =>
            HasClosedContext(CertifiedContexts(entryContexts', leaderViews', confirmations'), p, Part(formal'[r], p))
    BY ClosedPartitionHasCompleteContext, <1>4, <1>5
<1>8. \A h \in partitionHistory' \ partitionHistory :
          \E r \in Replicas : h.part \in Int /\ h.part < Cur(formal'[r])
            /\ h.entries = Part(formal'[r], h.part) /\ h.entries # {}
    BY SMT DEF Next, Observe, Partitions
<1>9. \A h \in appliedPartitionHistory' \ appliedPartitionHistory :
          \E r \in Replicas : h.part \in Int /\ h.part < Cur(formal'[r])
            /\ h.entries = Part(formal'[r], h.part) /\ h.entries # {}
    BY SMT, <1>6 DEF Next, Observe
<1> QED BY ONLY SMT, <1>3, <1>7, <1>8, <1>9
    DEF CertifiedPartitionHistory, ClosedPartitionOrigins

THEOREM CertifiedHistoriesStuttering ==
    ASSUME CertifiedPartitionHistory, UNCHANGED proofVars
    PROVE CertifiedPartitionHistory'
BY SMT DEF CertifiedPartitionHistory, CertifiedContexts, CertifiedLogEntries,
    ClosedPartitionOrigins, HasClosedContext, proofVars, vars, protocolVars, observerVars
=============================================================================
