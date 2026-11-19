---------------------- MODULE TRaftControlMakeReport ---------------------
EXTENDS TRaftControlSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM MakeReportPreservesControl ==
    ASSUME ElectionInvariant, ControlInvariant, ObserveWinners,
           NEW r \in Replicas, NEW req \in recoveryRequests, MakeReport(r, req)
    PROVE ControlInvariant'
<1>0. winners \subseteq winners'
    BY SMT DEF ObserveWinners
<1>00. ElectionInvariant'
    BY SMT, ElectionFramePreserves DEF MakeReport, ElectionCoreVars
<1>01. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
        /\ \A checkedReplica \in Replicas : term[checkedReplica] <= term'[checkedReplica]
    BY SMT, <1>00 DEF ElectionInvariant, ElectionTypes, Terms, MakeReport
<1>1. ControlShape'
    BY SMT, <1>0 DEF ControlInvariant, ControlShape,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         MakeReport, Reporters, EmptyReports, Phases, Roles, Terms
<1>2. ProposalProvenance'
    <2>1. OwnedEpochs(proposals, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, ProposalProvenance
    <2>2. OwnedEpochs(proposals' \ proposals, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, MakeReport, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF ProposalProvenance
<1>3. UnusedProposalEpoch'
    BY SMT, <1>0 DEF ControlInvariant, UnusedProposalEpoch, ProposalProvenance, OwnedEpochs,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         MakeReport, Reporters, EmptyReports, Phases, Roles, Terms
<1>4. RecoveryRequestProvenance'
    <2>1. OwnedEpochs(recoveryRequests, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, RecoveryRequestProvenance
    <2>2. OwnedEpochs(recoveryRequests' \ recoveryRequests, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, MakeReport, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF RecoveryRequestProvenance
<1>5. ReportProvenance'
    <2>1. ReportProvenance
        BY DEF ControlInvariant
    <2>2. term' = term /\ recoveryRequests' = recoveryRequests
          /\ term[r] = req.epoch
          /\ reportMessages' = reportMessages \cup
                {[sender |-> r, receiver |-> req.owner, epoch |-> req.epoch,
                  entries |-> formal[r], pending |-> IF MutDropPending THEN {} ELSE retained[r]]}
        BY DEF MakeReport
    <2>30. OwnedEpochs(recoveryRequests, term, winners)
        BY DEF ControlInvariant, RecoveryRequestProvenance
    <2>31. req.owner \in Replicas /\ req.epoch \in Terms \ {0}
        BY <2>30, OwnedEpochsMember
    <2>3. r \in Replicas /\ req \in recoveryRequests
          /\ req.owner \in Replicas /\ req.epoch \in Terms \ {0}
          /\ term \in [Replicas -> Nat]
        BY <1>01, <2>31
    <2>4. \A m \in reportMessages' :
          /\ m.sender \in Replicas /\ m.receiver \in Replicas
          /\ m.epoch \in Terms \ {0} /\ m.epoch <= term'[m.sender]
        BY ONLY SMT, <2>1, <2>2, <2>3 DEF ReportProvenance, Terms
    <2>5. ASSUME NEW m \in reportMessages'
          PROVE \E q \in recoveryRequests' : q.owner = m.receiver /\ q.epoch = m.epoch
        <3>1. CASE m \in reportMessages
            BY ONLY ZenonT(5), <2>1, <2>2, <3>1 DEF ReportProvenance
        <3>2. CASE m \notin reportMessages
            <4>1. m.receiver = req.owner /\ m.epoch = req.epoch
                BY ONLY SMT, <2>2, <2>5, <3>2
            <4>2. req \in recoveryRequests'
                BY ONLY SMT, <2>2, <2>3
            <4> QED BY ONLY <4>1, <4>2
        <3> QED BY <3>1, <3>2
    <2> QED BY <2>4, <2>5 DEF ReportProvenance
<1>6. CollectedReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, CollectedReportProvenance, ControlShape, ReportProvenance,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         MakeReport, Reporters, EmptyReports, Phases, Roles, Terms
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ControlInvariant
=============================================================================
