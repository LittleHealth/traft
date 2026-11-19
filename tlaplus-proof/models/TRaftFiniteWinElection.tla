----------------------- MODULE TRaftFiniteWinElection -----------------------
EXTENDS TRaftFiniteSupport

THEOREM WinElectionPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas,
           WinElection(c)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(recoveryRequests)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. recoveryRequests' = recoveryRequests \cup {[owner |-> c, epoch |-> term[c]]}
        BY DEF WinElection
    <2>12. IsFiniteSet(recoveryRequests')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, reportMessages, offers, proposals, ackMessages, confirmations, commitMessages>>
        BY DEF WinElection
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF WinElection, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF WinElection, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF WinElection, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
