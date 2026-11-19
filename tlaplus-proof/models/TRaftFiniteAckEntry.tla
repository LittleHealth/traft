----------------------- MODULE TRaftFiniteAckEntry -----------------------
EXTENDS TRaftFiniteSupport

THEOREM AckEntryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW o,
           AckEntry(r, o)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(ackMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. ackMessages' = ackMessages \cup {Ack(r, o.owner, o.epoch, o.entry, {o.entry})}
        BY DEF AckEntry
    <2>12. IsFiniteSet(ackMessages')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, proposals, confirmations, commitMessages>>
        BY DEF AckEntry
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF AckEntry, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF AckEntry, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF AckEntry, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
