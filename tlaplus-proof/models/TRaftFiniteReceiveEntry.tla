----------------------- MODULE TRaftFiniteReceiveEntry -----------------------
EXTENDS TRaftFiniteSupport

THEOREM ReceiveEntryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW o,
           ReceiveEntry(r, o)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF ReceiveEntry, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>1. FiniteMap(formal')
        <3>1. r \in Replicas /\ formal' = [formal EXCEPT ![r] = @ \cup {o.entry}]
            BY DEF ReceiveEntry
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>2. FiniteMap(stored')
        <3>1. r \in Replicas /\ stored' = [stored EXCEPT ![r] = @ \cup {o.entry}]
            BY DEF ReceiveEntry
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>3. FiniteMap(retained')
        BY SMT, <2>0 DEF ReceiveEntry
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        BY SMT, <2>0 DEF ReceiveEntry
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF ReceiveEntry, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF ReceiveEntry, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
