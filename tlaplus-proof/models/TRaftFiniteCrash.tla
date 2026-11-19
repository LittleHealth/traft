----------------------- MODULE TRaftFiniteCrash -----------------------
EXTENDS TRaftFiniteSupport

THEOREM CrashPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas,
           Crash(r)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF Crash, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF Crash, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF Crash, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF Crash, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
