---------------------- MODULE TRaftControlWinElection ---------------------
EXTENDS TRaftControlSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM WinElectionPreservesControl ==
    ASSUME ElectionInvariant, ControlInvariant, ObserveWinners,
           NEW c \in Replicas, WinElection(c)
    PROVE ControlInvariant'
<1>0. winners \subseteq winners'
    BY SMT DEF ObserveWinners
<1>00. ElectionInvariant'
    BY WinElectionPreservesElection
<1>01. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
        /\ \A r \in Replicas : term[r] <= term'[r]
    BY SMT, <1>00 DEF ElectionInvariant, ElectionTypes, Terms, WinElection
<1>1. ControlShape'
    BY SMT, <1>0 DEF ControlInvariant, ControlShape,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         WinElection, Reporters, EmptyReports, Phases, Roles, Terms
<1>2. ProposalProvenance'
    <2>1. OwnedEpochs(proposals, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, ProposalProvenance
    <2>2. OwnedEpochs(proposals' \ proposals, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, WinElection, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF ProposalProvenance
<1>3. UnusedProposalEpoch'
    <2>1. UnusedProposalEpoch /\ term' = term /\ proposals' = proposals
          /\ role \in [Replicas -> Roles] /\ phase \in [Replicas -> Phases]
          /\ role[c] = "Candidate" /\ c \in Replicas
          /\ role' = [role EXCEPT ![c] = "LeaderCandidate"]
          /\ phase' = [phase EXCEPT ![c] = "collect"]
        BY DEF ControlInvariant, ControlShape, ElectionInvariant, ElectionTypes, WinElection
    <2>2. \A checkedNode \in Replicas :
              (role'[checkedNode] = "Candidate" \/ phase'[checkedNode] = "collect") =>
                (role[checkedNode] = "Candidate" \/ phase[checkedNode] = "collect")
        BY ONLY SMT, <2>1
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF UnusedProposalEpoch
<1>4. RecoveryRequestProvenance'
    <2>1. OwnedEpochs(recoveryRequests, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, RecoveryRequestProvenance
    <2>2. OwnedEpochs(recoveryRequests' \ recoveryRequests, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, WinElection, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF RecoveryRequestProvenance
<1>5. ReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, ReportProvenance, RecoveryRequestProvenance, OwnedEpochs,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         WinElection, Reporters, EmptyReports, Phases, Roles, Terms
<1>6. CollectedReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, CollectedReportProvenance, ControlShape, ReportProvenance,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         WinElection, Reporters, EmptyReports, Phases, Roles, Terms
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ControlInvariant
=============================================================================
