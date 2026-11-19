----------------------- MODULE TRaftFiniteAckProposal -----------------------
EXTENDS TRaftFiniteSupport

THEOREM AckProposalPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW p,
           AckProposal(r, p)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(ackMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. ackMessages' = ackMessages \cup {Ack(r, p.owner, p.epoch, p.first, Result(p))}
        BY DEF AckProposal
    <2>12. IsFiniteSet(ackMessages')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, proposals, confirmations, commitMessages>>
        BY DEF AckProposal
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF AckProposal, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF AckProposal, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF AckProposal, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
