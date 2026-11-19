----------------------- MODULE TRaftClosedHistoryProof -----------------------
EXTENDS TRaftBoundaryCountSupport, TRaftClosedHistoryState
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM ClosedContextSurvivesHistoryGrowth ==
    ASSUME NEW E, NEW F, NEW p, NEW S, E \subseteq F, HasClosedContext(E, p, S)
    PROVE HasClosedContext(F, p, S)
BY SMT DEF HasClosedContext

THEOREM ClosedPartitionHasCompleteContext ==
    ASSUME NEW E, NEW L, NEW p \in Int, L \subseteq Entries, IsFiniteSet(L),
           \A e \in L : \E ctx \in E : ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1),
           p < Cur(L), Part(L, p) # {}
    PROVE HasClosedContext(E, p, Part(L, p))
<1>1. L # {}
    BY SMT DEF Part
<1>2. PICK e \in L : e.part = Cur(L)
    BY FiniteLogFrontier, <1>1
<1>3. e.part \in Int /\ e.part > p
    BY SMT, <1>2 DEF Entries, Partitions
<1>4. PICK ctx \in E :
          ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
    BY SMT, <1>2
<1>5. Part(Prefix(L, e.part - 1), p) = Part(L, p)
    BY ONLY SMT, <1>3 DEF Part, Prefix
<1> QED BY SMT, <1>3, <1>4, <1>5 DEF HasClosedContext

THEOREM ClosedHistoriesInitiallyComplete == ProofInit => HistoryPartitionCompleteness
BY SMT DEF ProofInit, Init, HistoryPartitionCompleteness, ClosedPartitionOrigins

THEOREM ClosedHistoriesInductiveStep ==
    ASSUME HistoryPartitionCompleteness, RecoveryInvariant', FiniteLogInvariant', Observe
    PROVE HistoryPartitionCompleteness'
<1>1. entryContexts \subseteq entryContexts'
    BY SMT DEF Observe
<1>2. \A h \in partitionHistory \cup appliedPartitionHistory :
          HasClosedContext(entryContexts', h.part, h.entries)
    BY SMT, <1>1, ClosedContextSurvivesHistoryGrowth
       DEF HistoryPartitionCompleteness, ClosedPartitionOrigins
<1>3. \A r \in Replicas : formal'[r] \subseteq Entries
          /\ IsFiniteSet(formal'[r]) /\ ContextSound(formal[r])'
    BY DEF RecoveryInvariant, TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData
<1>4. \A r \in Replicas : Cur(formal'[r]) \in Int
    BY FiniteLogPartitionFrontier, <1>3
<1>5. \A r \in Replicas : \A p \in Int :
          (p < Cur(formal'[r]) /\ Part(formal'[r], p) # {}) =>
            HasClosedContext(entryContexts', p, Part(formal'[r], p))
    BY ClosedPartitionHasCompleteContext, <1>3 DEF ContextSound
<1>6. \A h \in partitionHistory' \ partitionHistory :
          \E r \in Replicas : h.part \in Int /\ h.part < Cur(formal'[r])
            /\ h.entries = Part(formal'[r], h.part) /\ h.entries # {}
    BY SMT DEF Observe, Partitions
<1>7. \A h \in appliedPartitionHistory' \ appliedPartitionHistory :
          \E r \in Replicas : h.part \in Int /\ h.part < Cur(formal'[r])
            /\ h.entries = Part(formal'[r], h.part) /\ h.entries # {}
    BY SMT, <1>4 DEF Observe
<1> QED BY ONLY SMT, <1>2, <1>5, <1>6, <1>7
    DEF HistoryPartitionCompleteness, ClosedPartitionOrigins

THEOREM ClosedHistoriesStuttering ==
    ASSUME HistoryPartitionCompleteness, UNCHANGED proofVars
    PROVE HistoryPartitionCompleteness'
BY SMT DEF HistoryPartitionCompleteness, ClosedPartitionOrigins, HasClosedContext,
    proofVars, vars, protocolVars, observerVars
=============================================================================
