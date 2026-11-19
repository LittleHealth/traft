----------------------- MODULE TRaftFiniteAdoptTerm -----------------------
EXTENDS TRaftFiniteSupport

THEOREM AdoptTermPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW t,
           AdoptTerm(r, t)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF AdoptTerm, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF AdoptTerm, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF AdoptTerm, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF AdoptTerm, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
