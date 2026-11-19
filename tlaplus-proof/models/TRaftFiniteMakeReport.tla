----------------------- MODULE TRaftFiniteMakeReport -----------------------
EXTENDS TRaftFiniteSupport

THEOREM MakeReportPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW r \in Replicas, NEW req,
           MakeReport(r, req)
    PROVE FiniteLogInvariant'
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(reportMessages)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. reportMessages' = reportMessages \cup {[sender |-> r, receiver |-> req.owner, epoch |-> req.epoch, entries |-> formal[r], pending |-> IF MutDropPending THEN {} ELSE retained[r]]}
        BY DEF MakeReport
    <2>12. IsFiniteSet(reportMessages')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, offers, proposals, ackMessages, confirmations, commitMessages>>
        BY DEF MakeReport
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    BY SMT, FiniteNodeDataFrame DEF MakeReport, FiniteLogInvariant, FiniteNodeVars
<1>3. FiniteProposals'
    BY SMT, FiniteProposalsFrame DEF MakeReport, FiniteLogInvariant
<1>4. FiniteSnapshots'
    <2>0. FiniteSnapshots
        BY DEF FiniteLogInvariant
    <2>1. reportMessages' = reportMessages \cup
                 {[sender |-> r, receiver |-> req.owner, epoch |-> req.epoch,
                   entries |-> formal[r], pending |-> IF MutDropPending THEN {} ELSE retained[r]]}
          /\ voteRequests' = voteRequests /\ proposals' = proposals
        BY DEF MakeReport
    <2>2. IsFiniteSet(formal[r]) /\ IsFiniteSet(retained[r]) /\ retained[r] \subseteq proposals
        BY SMT DEF FiniteLogInvariant, FiniteNodeData
    <2>3. ASSUME NEW m \in reportMessages'
          PROVE IsFiniteSet(m.entries) /\ IsFiniteSet(m.pending) /\ m.pending \subseteq proposals'
        <3>1. CASE m \in reportMessages
            BY ONLY SMT, <2>0, <2>1, <3>1 DEF FiniteSnapshots
        <3>2. CASE m \notin reportMessages
            <4>1. m.entries = formal[r]
                  /\ m.pending = (IF MutDropPending THEN {} ELSE retained[r])
                  /\ proposals' = proposals
                BY ONLY SMT, <2>1, <2>3, <3>2
            <4>2. IsFiniteSet({})
                BY FS_EmptySet
            <4> QED BY ONLY SMT, <4>1, <4>2, <2>2
        <3> QED BY <3>1, <3>2
    <2>4. \A q \in voteRequests' : IsFiniteSet(q.entries)
        BY ONLY SMT, <2>0, <2>1 DEF FiniteSnapshots
    <2> QED BY <2>3, <2>4 DEF FiniteSnapshots

<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
