---------------------- MODULE TRaftControlCrash ---------------------
EXTENDS TRaftControlSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM CrashPreservesControl ==
    ASSUME ElectionInvariant, ControlInvariant, ObserveWinners,
           NEW r \in Replicas, Crash(r)
    PROVE ControlInvariant'
<1>0. winners \subseteq winners'
    BY SMT DEF ObserveWinners
<1>00. ElectionInvariant'
    BY CrashPreservesElection
<1>01. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
        /\ \A checkedReplica \in Replicas : term[checkedReplica] <= term'[checkedReplica]
    BY SMT, <1>00 DEF ElectionInvariant, ElectionTypes, Terms, Crash
<1>1. ControlShape'
    <2>1. ControlShape /\ role \in [Replicas -> Roles] /\ r \in Replicas
        BY DEF ControlInvariant, ElectionInvariant, ElectionTypes
    <2>2. role' = [role EXCEPT ![r] = "Follower"]
          /\ phase' = [phase EXCEPT ![r] = "idle"]
          /\ current' = [current EXCEPT ![r] = NoProposal]
          /\ reports' = [reports EXCEPT ![r] = EmptyReports]
          /\ term' = term /\ proposals' = proposals /\ reportMessages' = reportMessages
        BY DEF Crash
    <2>3. phase' \in [Replicas -> Phases]
        BY ONLY SMT, <2>1, <2>2 DEF ControlShape, Phases
    <2>4. current' \in [Replicas -> proposals' \cup {NoProposal}]
        BY ONLY SMT, <2>1, <2>2 DEF ControlShape
    <2>5. reports' \in [Replicas -> [Replicas -> reportMessages' \cup {NoReport}]]
        BY ONLY SMT, <2>1, <2>2 DEF ControlShape, EmptyReports
    <2>6. \A checkedNode \in Replicas :
              /\ (role'[checkedNode] = "Leader") <=> (phase'[checkedNode] = "serve")
              /\ (role'[checkedNode] = "LeaderCandidate") <=>
                    (phase'[checkedNode] \in {"collect", "sync", "commit"})
              /\ phase'[checkedNode] \in {"idle", "collect"} => current'[checkedNode] = NoProposal
              /\ phase'[checkedNode] \in {"sync", "commit", "serve"} =>
                    /\ current'[checkedNode] \in proposals'
                    /\ current'[checkedNode].owner = checkedNode
                    /\ current'[checkedNode].epoch = term'[checkedNode]
        BY ONLY SMT, <2>1, <2>2 DEF ControlShape
    <2> QED BY <2>3, <2>4, <2>5, <2>6 DEF ControlShape
<1>2. ProposalProvenance'
    <2>1. OwnedEpochs(proposals, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, ProposalProvenance
    <2>2. OwnedEpochs(proposals' \ proposals, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, Crash, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF ProposalProvenance
<1>3. UnusedProposalEpoch'
    <2>1. UnusedProposalEpoch /\ term' = term /\ proposals' = proposals
          /\ role \in [Replicas -> Roles] /\ phase \in [Replicas -> Phases]
          /\ role' = [role EXCEPT ![r] = "Follower"]
          /\ phase' = [phase EXCEPT ![r] = "idle"] /\ r \in Replicas
        BY DEF ControlInvariant, ControlShape, ElectionInvariant, ElectionTypes, Crash
    <2>2. \A checkedNode \in Replicas :
              (role'[checkedNode] = "Candidate" \/ phase'[checkedNode] = "collect") =>
                /\ checkedNode # r
                /\ role'[checkedNode] = role[checkedNode]
                /\ phase'[checkedNode] = phase[checkedNode]
        BY ONLY SMT, <2>1
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF UnusedProposalEpoch
<1>4. RecoveryRequestProvenance'
    <2>1. OwnedEpochs(recoveryRequests, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, RecoveryRequestProvenance
    <2>2. OwnedEpochs(recoveryRequests' \ recoveryRequests, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, Crash, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF RecoveryRequestProvenance
<1>5. ReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, ReportProvenance, RecoveryRequestProvenance, OwnedEpochs,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         Crash, Reporters, EmptyReports, Phases, Roles, Terms
<1>6. CollectedReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, CollectedReportProvenance, ControlShape, ReportProvenance,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         Crash, Reporters, EmptyReports, Phases, Roles, Terms
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ControlInvariant
=============================================================================
