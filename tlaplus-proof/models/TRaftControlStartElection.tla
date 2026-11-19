---------------------- MODULE TRaftControlStartElection ---------------------
EXTENDS TRaftControlSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM StartElectionPreservesControl ==
    ASSUME ElectionInvariant, ControlInvariant, ObserveWinners,
           NEW c \in Replicas, StartElection(c)
    PROVE ControlInvariant'
<1>0. winners \subseteq winners'
    BY SMT DEF ObserveWinners
<1>00. ElectionInvariant'
    BY StartElectionPreservesElection
<1>01. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
        /\ \A r \in Replicas : term[r] <= term'[r]
    BY SMT, <1>00 DEF ElectionInvariant, ElectionTypes, Terms, StartElection
<1>1. ControlShape'
    <2>1. ControlShape /\ role \in [Replicas -> Roles]
          /\ term \in [Replicas -> Terms] /\ c \in Replicas
        BY DEF ControlInvariant, ElectionInvariant, ElectionTypes
    <2>2. role' = [role EXCEPT ![c] = "Candidate"]
          /\ phase' = [phase EXCEPT ![c] = "idle"]
          /\ current' = [current EXCEPT ![c] = NoProposal]
          /\ reports' = [reports EXCEPT ![c] = EmptyReports]
          /\ term' = [term EXCEPT ![c] = term[c] + 1] /\ proposals' = proposals /\ reportMessages' = reportMessages
        BY DEF StartElection
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
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, StartElection, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF ProposalProvenance
<1>3. UnusedProposalEpoch'
    <2>1. UnusedProposalEpoch /\ c \in Replicas
          /\ role \in [Replicas -> Roles] /\ phase \in [Replicas -> Phases]
        BY SMT DEF ControlInvariant, ControlShape, ElectionInvariant, ElectionTypes
    <2>2. \A q \in proposals : q.owner \in Replicas /\ q.epoch \in Nat
                   /\ q.epoch <= term[q.owner]
        BY OwnedEpochsNumerical DEF ControlInvariant, ProposalProvenance
    <2>3. term' = [term EXCEPT ![c] = term[c] + 1]
          /\ role' = [role EXCEPT ![c] = "Candidate"]
          /\ phase' = [phase EXCEPT ![c] = "idle"] /\ proposals' = proposals
        BY SMT DEF StartElection, Proposal
    <2> QED BY ONLY SMT, <1>01, <2>1, <2>2, <2>3 DEF UnusedProposalEpoch
<1>4. RecoveryRequestProvenance'
    <2>1. OwnedEpochs(recoveryRequests, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, RecoveryRequestProvenance
    <2>2. OwnedEpochs(recoveryRequests' \ recoveryRequests, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, StartElection, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF RecoveryRequestProvenance
<1>5. ReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, ReportProvenance, RecoveryRequestProvenance, OwnedEpochs,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         StartElection, Reporters, EmptyReports, Phases, Roles, Terms
<1>6. CollectedReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, CollectedReportProvenance, ControlShape, ReportProvenance,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         StartElection, Reporters, EmptyReports, Phases, Roles, Terms
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ControlInvariant
=============================================================================
