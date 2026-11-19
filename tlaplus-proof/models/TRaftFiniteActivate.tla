----------------------- MODULE TRaftFiniteActivate -----------------------
EXTENDS TRaftFiniteSupport

THEOREM ActivatePreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas,
           Activate(c)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF Activate, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF Activate, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF Activate, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF Activate, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
