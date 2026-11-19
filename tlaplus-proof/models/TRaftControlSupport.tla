------------------------- MODULE TRaftControlSupport -------------------------
EXTENDS TRaftControlState, TRaftElectionTemporal
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM OwnedEpochsMember ==
    ASSUME NEW S, NEW T, NEW W, OwnedEpochs(S, T, W), NEW p \in S
    PROVE p.owner \in Replicas /\ p.epoch \in Terms \ {0}
          /\ p.epoch <= T[p.owner] /\ [node |-> p.owner, epoch |-> p.epoch] \in W
BY ZenonT(5) DEF OwnedEpochs

THEOREM OwnedEpochsMonotone ==
    ASSUME NEW S, NEW B \in [Replicas -> Nat], NEW A \in [Replicas -> Nat],
           NEW W, NEW V, W \subseteq V, OwnedEpochs(S, B, W),
           \A r \in Replicas : B[r] <= A[r]
    PROVE OwnedEpochs(S, A, V)
<1>1. ASSUME NEW p \in S
      PROVE p.owner \in Replicas /\ p.epoch \in Terms \ {0}
            /\ p.epoch <= A[p.owner]
            /\ [node |-> p.owner, epoch |-> p.epoch] \in V
    <2>1. p.owner \in Replicas /\ p.epoch \in Terms \ {0}
          /\ p.epoch <= B[p.owner]
          /\ [node |-> p.owner, epoch |-> p.epoch] \in W
        BY SMT DEF OwnedEpochs
    <2>2. p.epoch \in Nat /\ B[p.owner] \in Nat /\ A[p.owner] \in Nat
        BY SMT, <2>1 DEF Terms
    <2> QED BY SMT, <2>1, <2>2
<1> QED BY <1>1 DEF OwnedEpochs

THEOREM OwnedEpochsNumerical ==
    ASSUME NEW S, NEW T, NEW W, OwnedEpochs(S, T, W)
    PROVE \A p \in S : p.owner \in Replicas /\ p.epoch \in Nat
                       /\ p.epoch <= T[p.owner]
<1>1. ASSUME NEW p \in S
      PROVE p.owner \in Replicas /\ p.epoch \in Nat /\ p.epoch <= T[p.owner]
    <2>0. OwnedEpochs(S, T, W)
        OBVIOUS
    <2>1. p.owner \in Replicas /\ p.epoch \in Terms \ {0} /\ p.epoch <= T[p.owner]
        BY ONLY ZenonT(5), <2>0, <1>1 DEF OwnedEpochs
    <2>2. p.epoch \in Nat
        BY ONLY SMT, <2>1 DEF Terms
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1

THEOREM OwnedEpochsUnion ==
    ASSUME NEW S, NEW R, NEW T, NEW W,
           OwnedEpochs(S, T, W), OwnedEpochs(R \ S, T, W)
    PROVE OwnedEpochs(R, T, W)
BY ZenonT(10) DEF OwnedEpochs

THEOREM ControlInvariantInitially == Init => ControlInvariant
BY SMT DEF Init, ControlInvariant, ControlShape, ProposalProvenance,
           UnusedProposalEpoch, RecoveryRequestProvenance, ReportProvenance, OwnedEpochs,
           CollectedReportProvenance, Reporters, EmptyReports, Phases

THEOREM ControlStuttering ==
    ASSUME ControlInvariant, UNCHANGED ControlVars
    PROVE ControlInvariant'
BY SMT DEF ControlInvariant, ControlShape,
    ProposalProvenance, UnusedProposalEpoch, RecoveryRequestProvenance,
    ReportProvenance, CollectedReportProvenance, Reporters, ControlVars, ControlCoreVars

THEOREM ControlFrame ==
    ASSUME ControlInvariant, ElectionInvariant, ObserveWinners,
           UNCHANGED <<term, role, phase, current, proposals,
                       recoveryRequests, reportMessages, reports>>
    PROVE ControlInvariant'
<1>1. winners' = winners
    <2>1. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
        BY SMT DEF ElectionInvariant, ElectionWinnerFacts
    <2> QED BY ObservedWinnersAlreadyPresent, <2>1
<1> QED BY SMT, <1>1, ControlStuttering DEF ControlVars, ControlCoreVars

\* A new proposal can only come from the elected creator. The creator's
\* control phase records that it has not used this epoch for a proposal.
THEOREM RecoveryCreatorHasFreshEpoch ==
    ASSUME ControlInvariant, ElectionSafety, NEW c \in Replicas,
           role[c] = "LeaderCandidate", phase[c] = "collect",
           [node |-> c, epoch |-> term[c]] \in winners
    PROVE ~\E p \in proposals : p.epoch = term[c]
<1>1. ASSUME NEW p \in proposals, p.epoch = term[c]
      PROVE p.owner = c
    <2>1. [node |-> p.owner, epoch |-> p.epoch] \in winners
        BY SMT DEF ControlInvariant, ProposalProvenance, OwnedEpochs
    <2>2. [node |-> c, epoch |-> term[c]] \in winners /\ p.epoch = term[c]
        BY <1>1
    <2>3. \A a, b \in winners : a.epoch = b.epoch => a.node = b.node
        BY DEF ElectionSafety
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1> QED BY SMT, <1>1 DEF ControlInvariant, UnusedProposalEpoch
=============================================================================
