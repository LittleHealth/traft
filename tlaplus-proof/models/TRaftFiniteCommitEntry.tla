----------------------- MODULE TRaftFiniteCommitEntry -----------------------
EXTENDS TRaftFiniteSupport

THEOREM CommitEntryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW e,
           CommitEntry(c, e)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(commitMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. commitMessages' = commitMessages \cup {[owner |-> c, epoch |-> term[c], entry |-> e]}
        BY DEF CommitEntry
    <2>12. IsFiniteSet(commitMessages')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, proposals, ackMessages, confirmations>>
        BY DEF CommitEntry
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF CommitEntry, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF CommitEntry, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF CommitEntry, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
