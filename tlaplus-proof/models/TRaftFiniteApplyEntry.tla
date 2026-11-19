----------------------- MODULE TRaftFiniteApplyEntry -----------------------
EXTENDS TRaftFiniteSupport

THEOREM ApplyEntryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW e,
           ApplyEntry(r, e)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF ApplyEntry, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF ApplyEntry, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF ApplyEntry, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF ApplyEntry, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
