---------------------- MODULE TRaftControlBuildRecovery ---------------------
EXTENDS TRaftControlSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM BuildRecoveryPreservesControl ==
    ASSUME ElectionInvariant, ControlInvariant, ObserveWinners,
           NEW c \in Replicas, NEW p, BuildRecovery(c, p)
    PROVE ControlInvariant'
<1>0. winners \subseteq winners'
    BY SMT DEF ObserveWinners
<1>00. ElectionInvariant'
    BY SMT, ElectionFramePreserves DEF BuildRecovery, ElectionCoreVars
<1>01. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
        /\ \A r \in Replicas : term[r] <= term'[r]
    BY SMT, <1>00 DEF ElectionInvariant, ElectionTypes, Terms, BuildRecovery
<1>1. ControlShape'
    BY SMT, <1>0 DEF ControlInvariant, ControlShape,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         BuildRecovery, Reporters, EmptyReports, Phases, Roles, Terms, Entry, Proposal
<1>2. ProposalProvenance'
    <2>1. OwnedEpochs(proposals, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, ProposalProvenance
    <2>2. OwnedEpochs(proposals' \ proposals, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, BuildRecovery, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF ProposalProvenance
<1>3. UnusedProposalEpoch'
    <2>1. UnusedProposalEpoch /\ c \in Replicas
          /\ role \in [Replicas -> Roles] /\ phase \in [Replicas -> Phases]
        BY SMT DEF ControlInvariant, ControlShape, ElectionInvariant, ElectionTypes
    <2>2. \A q \in proposals : q.owner \in Replicas /\ q.epoch \in Nat
                   /\ q.epoch <= term[q.owner]
        BY OwnedEpochsNumerical DEF ControlInvariant, ProposalProvenance
    <2>3. term' = term /\ role' = role
          /\ role[c] = "LeaderCandidate"
          /\ phase' = [phase EXCEPT ![c] = "sync"]
          /\ proposals \subseteq proposals'
          /\ \A q \in proposals' \ proposals : q.owner = c
        BY SMT DEF BuildRecovery, Proposal
    <2> QED BY ONLY SMT, <1>01, <2>1, <2>2, <2>3 DEF UnusedProposalEpoch
<1>4. RecoveryRequestProvenance'
    <2>1. OwnedEpochs(recoveryRequests, term', winners')
        BY SMT, <1>0, <1>01, OwnedEpochsMonotone DEF ControlInvariant, RecoveryRequestProvenance
    <2>2. OwnedEpochs(recoveryRequests' \ recoveryRequests, term', winners')
        BY SMT, <1>0, <1>00, <1>01 DEF OwnedEpochs, BuildRecovery, Proposal,
           ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, Terms
    <2> QED BY OwnedEpochsUnion, <2>1, <2>2 DEF RecoveryRequestProvenance
<1>5. ReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, ReportProvenance, RecoveryRequestProvenance, OwnedEpochs,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         BuildRecovery, Reporters, EmptyReports, Phases, Roles, Terms, Entry, Proposal
<1>6. CollectedReportProvenance'
    BY SMT, <1>0 DEF ControlInvariant, CollectedReportProvenance, ControlShape, ReportProvenance,
         ElectionInvariant, ElectionTypes, ElectionWinnerFacts,
         BuildRecovery, Reporters, EmptyReports, Phases, Roles, Terms, Entry, Proposal
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ControlInvariant
=============================================================================
