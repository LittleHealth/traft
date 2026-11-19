----------------------- MODULE TRaftFiniteDeliverReport -----------------------
EXTENDS TRaftFiniteSupport

THEOREM DeliverReportPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW m,
           DeliverReport(c, m)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF DeliverReport, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF DeliverReport, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF DeliverReport, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF DeliverReport, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
