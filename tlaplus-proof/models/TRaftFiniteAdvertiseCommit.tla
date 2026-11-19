----------------------- MODULE TRaftFiniteAdvertiseCommit -----------------------
EXTENDS TRaftFiniteSupport

THEOREM AdvertiseCommitPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW e,
           AdvertiseCommit(c, e)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(commitMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. commitMessages' = commitMessages \cup {[owner |-> c, epoch |-> term[c], entry |-> e]}
        BY DEF AdvertiseCommit
    <2>12. IsFiniteSet(commitMessages')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, proposals, ackMessages, confirmations>>
        BY DEF AdvertiseCommit
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF AdvertiseCommit, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF AdvertiseCommit, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF AdvertiseCommit, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
