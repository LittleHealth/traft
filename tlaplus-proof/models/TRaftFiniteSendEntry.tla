----------------------- MODULE TRaftFiniteSendEntry -----------------------
EXTENDS TRaftFiniteSupport

THEOREM SendEntryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW e,
           SendEntry(c, e)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(offers)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. offers' = offers \cup {NormalMessage(c, e)}
        BY DEF SendEntry
    <2>12. IsFiniteSet(offers')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, proposals, ackMessages, confirmations, commitMessages>>
        BY DEF SendEntry
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF SendEntry, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF SendEntry, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF SendEntry, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
