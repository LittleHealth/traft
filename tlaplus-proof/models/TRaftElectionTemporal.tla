------------------------- MODULE TRaftElectionTemporal -----------------------
EXTENDS TRaftElectionFrames, TRaftElectionStartElection,
        TRaftElectionAdoptTerm, TRaftElectionGrantVote,
        TRaftElectionDeliverVote, TRaftElectionWinElection,
        TRaftElectionActivate, TRaftElectionCrash

THEOREM ElectionInductiveStep ==
    ASSUME ElectionInvariant, Next
    PROVE ElectionInvariant'
<1>1. ObserveWinners /\ ProtocolNext
    BY SMT, WinnerObservationProjection DEF Next
<1>2. ElectionChangingNext \/ UNCHANGED ElectionCoreVars
    BY ProtocolElectionProjection, <1>1
<1> QED BY SMT, <1>1, <1>2, StartElectionPreservesElection,
           AdoptTermPreservesElection, GrantVotePreservesElection,
           DeliverVotePreservesElection, WinElectionPreservesElection,
           ActivatePreservesElection, CrashPreservesElection, ElectionFramePreserves
    DEF ElectionChangingNext

THEOREM ElectionInvariantAlways == Spec => []ElectionInvariant
<1>1. Init => ElectionInvariant
    BY ElectionInvariantInitially
<1>2. ElectionInvariant /\ [Next]_vars => ElectionInvariant'
    BY SMT, ElectionInductiveStep, ElectionStuttering, ProtocolStutterProjectsToElection
<1> QED BY PTL, <1>1, <1>2 DEF Spec

THEOREM ProtocolElectionSafety == Spec => []ElectionSafety
BY PTL, ElectionInvariantAlways, ElectionInvariantImpliesElectionSafety
=============================================================================
