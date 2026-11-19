----------------------- MODULE TRaftFiniteLearnConfirmation -----------------------
EXTENDS TRaftFiniteSupport

THEOREM LearnConfirmationPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW p,
           LearnConfirmation(r, p)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF LearnConfirmation, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>01. p \in proposals
        BY SMT, <2>0 DEF LearnConfirmation
    <2>02. IsFiniteSet(Publish(r, p))
        BY SMT, <2>0, <2>01 DEF FiniteLogInvariant, FiniteProposals, FiniteMap, Publish
    <2>1. FiniteMap(formal')
        <3>1. r \in Replicas /\ formal' = [formal EXCEPT ![r] = Publish(r, p)]
            BY DEF LearnConfirmation
        <3> QED BY ONLY FiniteMapReplace, <2>0, <2>02, <3>1
    <2>2. FiniteMap(stored')
        BY SMT, <2>0 DEF LearnConfirmation
    <2>3. FiniteMap(retained')
        BY SMT, <2>0 DEF LearnConfirmation
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        BY SMT, <2>0 DEF LearnConfirmation
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF LearnConfirmation, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF LearnConfirmation, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
