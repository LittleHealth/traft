----------------------- MODULE TRaftFiniteGrantVote -----------------------
EXTENDS TRaftFiniteSupport

THEOREM GrantVotePreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW req,
           GrantVote(r, req)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>1. IsFiniteSet(voteMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>2. voteMessages' = voteMessages \cup
                     {[sender |-> r, receiver |-> req.candidate, epoch |-> req.epoch]}
          /\ UNCHANGED <<voteRequests, recoveryRequests, reportMessages, offers,
                         proposals, ackMessages, confirmations, commitMessages>>
        BY DEF GrantVote
    <2>3. IsFiniteSet(voteMessages')
        BY ONLY FiniteInsert, <2>1, <2>2
    <2> QED BY ONLY SMT, <2>0, <2>2, <2>3 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF GrantVote, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF GrantVote, FiniteLogInvariant
<1>4. FiniteSnapshots'
    BY SMT, FiniteSnapshotsFrame DEF GrantVote, FiniteLogInvariant, FiniteSnapshotVars
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
