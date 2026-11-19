----------------------- MODULE TRaftControlTemporal -----------------------
EXTENDS TRaftControlFrames,
        TRaftControlStartElection,
        TRaftControlAdoptTerm,
        TRaftControlWinElection,
        TRaftControlBuildRecovery,
        TRaftControlMakeReport,
        TRaftControlDeliverReport,
        TRaftControlConfirmProposal,
        TRaftControlActivate,
        TRaftControlCrash

THEOREM ControlInductiveStep ==
    ASSUME ElectionInvariant, ControlInvariant, Next
    PROVE ControlInvariant'
<1>1. ObserveWinners /\ ProtocolNext
    BY SMT, WinnerObservationProjection DEF Next
<1>2. ControlChangingNext \/ UNCHANGED ControlCoreVars
    BY ProtocolControlProjection, <1>1
<1> QED BY SMT, <1>1, <1>2, ControlFrame,
           StartElectionPreservesControl,
           AdoptTermPreservesControl,
           WinElectionPreservesControl,
           BuildRecoveryPreservesControl,
           MakeReportPreservesControl,
           DeliverReportPreservesControl,
           ConfirmProposalPreservesControl,
           ActivatePreservesControl,
           CrashPreservesControl
    DEF ControlChangingNext, ControlCoreVars

THEOREM ControlInvariantAlways == Spec => []ControlInvariant
<1>1. Spec => []ElectionInvariant
    BY ElectionInvariantAlways
<1>2. Init => ControlInvariant
    BY ControlInvariantInitially
<1>3. ElectionInvariant /\ ControlInvariant /\ [Next]_vars => ControlInvariant'
    BY SMT, ControlInductiveStep, ControlStuttering, ProtocolStutterProjectsToControl
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
