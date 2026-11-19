----------------------- MODULE TRaftFiniteRetainProposal -----------------------
EXTENDS TRaftFiniteSupport

THEOREM RetainProposalPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW p,
           RetainProposal(r, p)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    BY SMT, FiniteChannelsFrame DEF RetainProposal, FiniteLogInvariant, FiniteChannelVars
<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>1. FiniteMap(formal')
        BY SMT, <2>0 DEF RetainProposal
    <2>2. FiniteMap(stored')
        BY SMT, <2>0 DEF RetainProposal
    <2>3. FiniteMap(retained')
        <3>1. r \in Replicas /\ retained' = [retained EXCEPT ![r] = @ \cup {p}]
            BY DEF RetainProposal
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        BY SMT, <2>0 DEF RetainProposal
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF RetainProposal, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF RetainProposal, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
