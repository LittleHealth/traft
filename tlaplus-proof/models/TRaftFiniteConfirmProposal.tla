----------------------- MODULE TRaftFiniteConfirmProposal -----------------------
EXTENDS TRaftFiniteSupport

THEOREM ConfirmProposalPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas,
           ConfirmProposal(c)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(confirmations)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. confirmations' = confirmations \cup {current[c]}
        BY DEF ConfirmProposal
    <2>12. IsFiniteSet(confirmations')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, proposals, ackMessages, commitMessages>>
        BY DEF ConfirmProposal
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>01. current[c] \in proposals
        BY SMT, <2>0 DEF ConfirmProposal
    <2>02. IsFiniteSet(Publish(c, current[c]))
        BY SMT, <2>0, <2>01 DEF FiniteLogInvariant, FiniteProposals, FiniteMap, Publish
    <2>1. FiniteMap(formal')
        <3>1. c \in Replicas /\ formal' = [formal EXCEPT ![c] = Publish(c, current[c])]
            BY DEF ConfirmProposal
        <3> QED BY ONLY FiniteMapReplace, <2>0, <2>02, <3>1
    <2>2. FiniteMap(stored')
        BY SMT, <2>0 DEF ConfirmProposal
    <2>3. FiniteMap(retained')
        BY SMT, <2>0 DEF ConfirmProposal
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        BY SMT, <2>0 DEF ConfirmProposal
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF ConfirmProposal, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF ConfirmProposal, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
