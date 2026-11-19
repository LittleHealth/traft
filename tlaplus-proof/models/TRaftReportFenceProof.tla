------------------------ MODULE TRaftReportFenceProof ------------------------
EXTENDS TRaftInvariantDefinitions, TRaftTermAndVoteProof, TRaftOriginFrames, TRaftRetainedFrames,
        TRaftProposalIdentityProof
USE FormalFaultsDisabled, ParameterAssumptions DEF FormalFaultsDisabled, ParameterAssumptions

RetainedEpochFence(R, T) == \A r \in Replicas : \A p \in R[r] : p.epoch <= T[r]
SnapshotFence(M, R) == \A m \in M :
    /\ m.sender \in Replicas /\ m.epoch \in Terms \ {0}
    /\ m.pending \subseteq R[m.sender]
    /\ \A p \in R[m.sender] : p.epoch < m.epoch => p \in m.pending
ProposalFence(P, T) == \A p \in P : Quorum({r \in Replicas : T[r] >= p.epoch})

THEOREM FenceQuorumUpward ==
    ASSUME NEW S, NEW T, Quorum(S), S \subseteq T, T \subseteq Replicas
    PROVE Quorum(T)
BY SMT, MajorityUpward DEF Quorum, Majority

THEOREM RetainedEpochFenceStep ==
    ASSUME ProofInvariant, ProtocolNext, term' \in [Replicas -> Terms],
           \A r \in Replicas : term[r] <= term'[r]
    PROVE RetainedEpochFence(retained', term')
<1>1. retained = [r \in Replicas |-> retained[r]]
      /\ term \in [Replicas -> Nat]
      /\ \A r \in Replicas : \A p \in retained[r] : p.epoch \in Nat /\ p.epoch <= term[r]
    <2>1. retained \in [Replicas -> SUBSET proposals] /\ term \in [Replicas -> Terms]
          /\ \A p \in proposals : p.epoch \in Terms
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. \A r \in Replicas : \A p \in retained[r] : p.epoch <= term[r]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences
    <2>3. Terms \subseteq Nat
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1>2. \A r \in Replicas : \A p \in retained'[r] \ retained[r] : p.epoch = term[r]
    BY RetainedChangeHasCurrentEpoch, <1>1
<1> QED BY SMT, <1>1, <1>2 DEF RetainedEpochFence, Terms

THEOREM ExistingSnapshotsSurviveRetaining ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE SnapshotFence(reportMessages, retained')
<1>1. retained = [r \in Replicas |-> retained[r]]
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. (\A r \in Replicas : retained[r] \subseteq retained'[r])
      /\ (\A r \in Replicas : \A p \in retained'[r] \ retained[r] : p.epoch = term[r])
    BY RetainedChangeHasCurrentEpoch, <1>1
<1>3. \A m \in reportMessages : m.epoch \in Nat /\ m.sender \in Replicas
          /\ m.epoch <= term[m.sender] /\ term[m.sender] \in Nat
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
        ReportFences, TermAndVoteFacts, TypeOK, Terms
<1>4. SnapshotFence(reportMessages, retained)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences, SnapshotFence
<1> QED BY ONLY SMT, <1>2, <1>3, <1>4 DEF SnapshotFence

THEOREM NewReportHasSnapshotFence ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW req, MakeReport(r, req)
    PROVE SnapshotFence(reportMessages', retained')
<1>1. SnapshotFence(reportMessages, retained)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences, SnapshotFence
<1>10. req \in recoveryRequests
    BY DEF MakeReport
<1>11. \A q \in recoveryRequests : q.epoch \in Terms \ {0}
    BY DEF ProofInvariant, PreProvenanceInvariant, ControlInvariant, RecoveryRequestProvenance, OwnedEpochs
<1>2. req \in recoveryRequests /\ req.epoch \in Terms \ {0}
    BY ONLY <1>10, <1>11
<1>3. reportMessages' = reportMessages \cup
          {[sender |-> r, receiver |-> req.owner, epoch |-> req.epoch,
            entries |-> formal[r], pending |-> retained[r]]}
      /\ UNCHANGED retained
    BY SMT DEF MakeReport
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3 DEF SnapshotFence

THEOREM ReportSnapshotFenceStep ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE SnapshotFence(reportMessages', retained')
<1>1. (\E r \in Replicas : \E req : MakeReport(r, req)) \/ UNCHANGED reportMessages
    BY ReportAnchorActionProjection
<1>2. SnapshotFence(reportMessages, retained')
    BY ExistingSnapshotsSurviveRetaining
<1> QED BY SMT, <1>1, <1>2, NewReportHasSnapshotFence

THEOREM ProposalFencesSurviveTermGrowth ==
    ASSUME NEW P, NEW T \in [Replicas -> Nat], NEW U \in [Replicas -> Nat],
           \A r \in Replicas : T[r] <= U[r],
           \A p \in P : p.epoch \in Nat, ProposalFence(P, T)
    PROVE ProposalFence(P, U)
<1>1. \A p \in P : {r \in Replicas : T[r] >= p.epoch} \subseteq
                        {r \in Replicas : U[r] >= p.epoch}
    BY SMT
<1>2. ProposalFence(P, T)
    OBVIOUS
<1>3. ASSUME NEW p \in P
      PROVE Quorum({r \in Replicas : U[r] >= p.epoch})
    <2>1. Quorum({r \in Replicas : T[r] >= p.epoch})
          /\ {r \in Replicas : T[r] >= p.epoch} \subseteq {r \in Replicas : U[r] >= p.epoch}
        BY <1>1, <1>2, <1>3 DEF ProposalFence
    <2>2. {r \in Replicas : U[r] >= p.epoch} \subseteq Replicas
        BY SMT
    <2> QED BY ONLY FenceQuorumUpward, <2>1, <2>2
<1> QED BY <1>3 DEF ProposalFence

THEOREM NewRecoveryHasProposalFence ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE ProposalFence(proposals', term')
<1>1. Quorum(Reporters(c)) /\ \A r \in Reporters(c) : term[r] >= term[c]
    BY ReportsFenceEarlierTerms DEF BuildRecovery
<1>2. Reporters(c) \subseteq {r \in Replicas : term[r] >= term[c]}
    BY ONLY SMT, <1>1 DEF Quorum
<1>3. Quorum({r \in Replicas : term[r] >= term[c]})
    BY ONLY SMT, FenceQuorumUpward, <1>1, <1>2
<1>4. UNCHANGED term /\ \A p \in proposals' \ proposals : p.epoch = term[c]
    BY SMT DEF BuildRecovery, Proposal
<1>5. ProposalFence(proposals, term)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences, ProposalFence
<1>6. term' = term
    BY ONLY <1>4
<1>7. ASSUME NEW p \in proposals'
      PROVE Quorum({r \in Replicas : term'[r] >= p.epoch})
    <2>1. CASE p \in proposals
        BY ONLY ZenonT(5), <1>5, <1>6, <1>7, <2>1 DEF ProposalFence
    <2>2. CASE p \notin proposals
        <3>1. p.epoch = term[c]
            BY ONLY <1>4, <1>7, <2>2
        <3> QED BY ONLY ZenonT(5), <1>3, <1>6, <3>1
    <2> QED BY <2>1, <2>2
<1> QED BY ONLY <1>7 DEF ProposalFence

THEOREM ReportFencesInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE ReportFences'
<1>1. ProofInvariant /\ ProtocolNext /\ ControlInvariant' /\ ElectionInvariant'
    BY ControlInductiveStep, ElectionInductiveStep
       DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext, Next
<1>2. term' \in [Replicas -> Terms] /\ \A r \in Replicas : term[r] <= term'[r]
    BY CandidateStepHasMonotonicFacts, <1>1 DEF StepFacts, ElectionInvariant, ElectionTypes
<1>3. RetainedEpochFence(retained', term') /\ SnapshotFence(reportMessages', retained')
    BY RetainedEpochFenceStep, ReportSnapshotFenceStep, <1>1, <1>2
<1>40. term \in [Replicas -> Terms] /\ (\A p \in proposals : p.epoch \in Terms \ {0})
       /\ ProposalFence(proposals, term)
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, ReportFences, ProposalFence
<1>41. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
       /\ \A p \in proposals : p.epoch \in Nat
    BY ONLY SMT, <1>40, <1>2 DEF Terms
<1>4. ProposalFence(proposals, term')
    BY ONLY ProposalFencesSurviveTermGrowth, <1>40, <1>41, <1>2
<1>5. (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
          \/ UNCHANGED proposals
    BY OnlyRecoveryCreatesProposal, <1>1
<1>6. ProposalFence(proposals', term')
    BY SMT, <1>1, <1>4, <1>5, NewRecoveryHasProposalFence
<1> QED BY ONLY SMT, <1>1, <1>3, <1>6 DEF ReportFences, RetainedEpochFence,
    SnapshotFence, ProposalFence, ControlInvariant, CollectedReportProvenance
=============================================================================
