------------------------- MODULE TRaftReportSublogProof ----------------------
EXTENDS TRaftSublogSupport, TRaftOriginFrames, TRaftHistoryRefinementProof

ReportSublogs(M, C, P) == \A m \in M : SublogIn(m.entries, C, P)

THEOREM CandidateReportedLogTypes == ProofInvariant =>
    \A m \in reportMessages : m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
        /\ SublogIn(m.entries, canonical, proposals)
<1>1. ASSUME ProofInvariant, NEW m \in reportMessages
      PROVE m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
            /\ SublogIn(m.entries, canonical, proposals)
    <2>1. Sublog(m.entries) /\ IsFiniteSet(m.entries)
          /\ canonical \in [Terms -> SUBSET Entries]
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape,
           FiniteLogInvariant, FiniteSnapshots
    <2> QED BY SMT, <2>1 DEF Sublog, SublogIn
<1> QED BY <1>1

THEOREM NewReportsHaveOldSublogs ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE \A m \in reportMessages' : m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
        /\ SublogIn(m.entries, canonical, proposals)
<1>1. \A m \in reportMessages : m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
          /\ SublogIn(m.entries, canonical, proposals)
    BY CandidateReportedLogTypes
<1>2. \A r \in Replicas : formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
          /\ SublogIn(formal[r], canonical, proposals)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape,
       FiniteLogInvariant, FiniteNodeData, Sublog, SublogIn
<1>3. (\E r \in Replicas : \E req : MakeReport(r, req)) \/ UNCHANGED reportMessages
    BY ReportAnchorActionProjection
<1>4. \A r \in Replicas : \A req : MakeReport(r, req) =>
          \A m \in reportMessages' \ reportMessages : m.entries = formal[r]
    BY SMT DEF MakeReport
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4

THEOREM ReportSublogsInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ProofNext, term' \in [Replicas -> Terms]
    PROVE ReportSublogs(reportMessages', canonical', proposals')
<1>1. ProtocolNext /\ GhostNext
    BY DEF ProofNext, Next
<1>2. \A m \in reportMessages' : m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
          /\ SublogIn(m.entries, canonical, proposals)
    BY NewReportsHaveOldSublogs, <1>1
<1>3. CanonicalPrefixesPersist(canonical, canonical')
    BY CanonicalPrefixesInductiveStep
<1>4. proposals \subseteq proposals'
    BY ProposalsNeverShrink, <1>1
<1>6. proposals \subseteq proposals' /\ \A t \in Terms : canonical[t] \subseteq canonical'[t]
    BY SMT, <1>1, <1>4 DEF GhostNext
<1> QED BY SublogTransport, <1>2, <1>3, <1>6 DEF ReportSublogs
=============================================================================
