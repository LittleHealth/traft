----------------------- MODULE TRaftFiniteStartElection -----------------------
EXTENDS TRaftFiniteSupport

THEOREM StartElectionPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas,
           StartElection(c)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(voteRequests)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. voteRequests' = voteRequests \cup {[candidate |-> c, epoch |-> term[c] + 1, entries |-> formal[c]]}
        BY DEF StartElection
    <2>12. IsFiniteSet(voteRequests')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>20. IsFiniteSet(voteMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>21. voteMessages' = voteMessages \cup {[sender |-> c, receiver |-> c, epoch |-> term[c] + 1]}
        BY DEF StartElection
    <2>22. IsFiniteSet(voteMessages')
        BY ONLY FiniteInsert, <2>20, <2>21
    <2>9. UNCHANGED <<recoveryRequests, reportMessages, offers, proposals, ackMessages, confirmations, commitMessages>>
        BY DEF StartElection
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>22, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF StartElection, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF StartElection, FiniteLogInvariant
<1>4. FiniteSnapshots'
    <2>0. FiniteSnapshots
        BY DEF FiniteLogInvariant
    <2>1. voteRequests' = voteRequests \cup
                 {[candidate |-> c, epoch |-> term[c] + 1, entries |-> formal[c]]}
          /\ reportMessages' = reportMessages /\ proposals' = proposals
        BY DEF StartElection
    <2>2. IsFiniteSet(formal[c])
        BY SMT DEF FiniteLogInvariant, FiniteNodeData
    <2> QED BY ONLY SMT, <2>0, <2>1, <2>2 DEF FiniteSnapshots

<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
