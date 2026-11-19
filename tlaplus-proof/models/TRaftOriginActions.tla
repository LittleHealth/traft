-------------------------- MODULE TRaftOriginActions ------------------------
EXTENDS TRaftOriginFrames

AlignedNodeUpdate(r) ==
    /\ Aligned(r, term[r])'
    /\ \A s \in Replicas \ {r} : formal'[s] = formal[s] /\ retained[s] \subseteq retained'[s]

THEOREM CreateEntryKeepsAlignment ==
    ASSUME TypeOK, NEW r \in Replicas, NEW v, CreateEntry(r, v)
    PROVE AlignedNodeUpdate(r)
BY SMT DEF CreateEntry, AlignedNodeUpdate, Aligned, TypeOK

THEOREM CreateSuccessorKeepsAlignment ==
    ASSUME TypeOK, NEW r \in Replicas, NEW v, NEW k, CreateSuccessor(r, v, k)
    PROVE AlignedNodeUpdate(r)
BY SMT DEF CreateSuccessor, AlignedNodeUpdate, Aligned, TypeOK

THEOREM ReceiveEntryKeepsAlignment ==
    ASSUME TypeOK, NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
    PROVE AlignedNodeUpdate(r)
BY SMT DEF ReceiveEntry, AlignedNodeUpdate, Aligned, TypeOK, CanReceive

THEOREM ConfirmProposalKeepsAlignment ==
    ASSUME TypeOK, NEW r \in Replicas, ConfirmProposal(r)
    PROVE AlignedNodeUpdate(r)
BY SMT DEF ConfirmProposal, AlignedNodeUpdate, Aligned, TypeOK, Publish, Result

THEOREM LearnConfirmationKeepsAlignment ==
    ASSUME TypeOK, NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
    PROVE AlignedNodeUpdate(r)
BY SMT DEF LearnConfirmation, AlignedNodeUpdate, Aligned, TypeOK, Publish, Result

THEOREM ProtocolKeepsFormalAnchors ==
    ASSUME ProofInvariant, RecoveryInvariant', FiniteLogInvariant', ProtocolNext
    PROVE FormalAnchors(formal', retained')
<1>1. FormalAnchors(formal, retained) /\ TypeOK
    BY SMT, OriginFactsDecompose DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>2. FormalAnchorChanges \/
          (UNCHANGED formal /\ \A r \in Replicas : retained[r] \subseteq retained'[r])
    BY FormalAnchorActionProjection, <1>1
<1>3. FormalAnchorChanges => \E r \in Replicas : AlignedNodeUpdate(r)
    BY SMT, <1>1, CreateEntryKeepsAlignment, CreateSuccessorKeepsAlignment,
       ReceiveEntryKeepsAlignment, ConfirmProposalKeepsAlignment,
       LearnConfirmationKeepsAlignment DEF FormalAnchorChanges
<1>4. CASE \E r \in Replicas : AlignedNodeUpdate(r)
    BY SMT, <1>1, <1>4, ChangedNodeWithAlignmentKeepsFormalAnchors DEF AlignedNodeUpdate
<1>5. CASE UNCHANGED formal /\ \A r \in Replicas : retained[r] \subseteq retained'[r]
    BY UnchangedFormalGrowingRetainedKeepsAnchors, <1>1, <1>5
<1> QED BY <1>2, <1>3, <1>4, <1>5

THEOREM MakeReportKeepsReportAnchors ==
    ASSUME ~MutDropPending, ProofInvariant, NEW r \in Replicas,
           NEW req, MakeReport(r, req)
    PROVE ReportAnchors(reportMessages')
<1>1. ReportAnchors(reportMessages) /\ FormalAnchors(formal, retained)
    BY SMT, OriginFactsDecompose DEF ProofInvariant, PreProvenanceInvariant
<1>2. \A p \in retained[r] : p.epoch <= term[r]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences
<1>3. HasAnchor(formal[r], retained[r])
    BY <1>1 DEF FormalAnchors
<1> QED BY SMT, <1>1, <1>2, <1>3 DEF MakeReport, ReportAnchors

THEOREM ProtocolKeepsReportAnchors ==
    ASSUME ~MutDropPending, ProofInvariant, ProtocolNext
    PROVE ReportAnchors(reportMessages')
<1>1. (\E r \in Replicas : \E req : MakeReport(r, req)) \/ UNCHANGED reportMessages
    BY ReportAnchorActionProjection
<1>2. CASE UNCHANGED reportMessages
    BY SMT, <1>2, OriginFactsDecompose DEF ProofInvariant, PreProvenanceInvariant
<1>3. CASE \E r \in Replicas : \E req : MakeReport(r, req)
    BY SMT, <1>3, MakeReportKeepsReportAnchors
<1> QED BY <1>1, <1>2, <1>3
=============================================================================
