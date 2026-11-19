----------------------- MODULE TRaftFiniteCreateSuccessor -----------------------
EXTENDS TRaftFiniteSupport

THEOREM CreateSuccessorPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW v, NEW k,
           CreateSuccessor(c, v, k)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF CreateSuccessor, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>1. FiniteMap(formal')
        <3>1. c \in Replicas /\ formal' = [formal EXCEPT ![c] = @ \cup {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]) + 1, v, k,
                     Count(formal[c], Cur(formal[c])))}]
            BY DEF CreateSuccessor
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>2. FiniteMap(stored')
        <3>1. c \in Replicas /\ stored' = [stored EXCEPT ![c] = @ \cup {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]) + 1, v, k,
                     Count(formal[c], Cur(formal[c])))}]
            BY DEF CreateSuccessor
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>3. FiniteMap(retained')
        BY SMT, <2>0 DEF CreateSuccessor
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        BY SMT, <2>0 DEF CreateSuccessor
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF CreateSuccessor, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF CreateSuccessor, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
