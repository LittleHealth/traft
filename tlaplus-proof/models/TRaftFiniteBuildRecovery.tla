----------------------- MODULE TRaftFiniteBuildRecovery -----------------------
EXTENDS TRaftFiniteSupport

THEOREM BuildRecoveryPreservesFiniteLogs ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas, NEW p \in Latest(ReportedProposals(c)) \cup {NoProposal},
           BuildRecovery(c, p)
    PROVE FiniteLogInvariant'
<1>0. IsFiniteSet(Recovered(c, p))
    BY RecoveryResultFinite
<1>1. FiniteChannels'
    <2>0. FiniteChannels
        BY DEF FiniteLogInvariant
    <2>10. IsFiniteSet(proposals)
        BY ONLY SMT, <2>0 DEF FiniteChannels
    <2>11. proposals' = proposals \cup {Proposal(c, term[c], Recovered(c, p),
                Entry(LastIndex(Recovered(c, p)) + 1, term[c], Cur(Recovered(c, p)) + 1,
                      NoValue, "noop", Count(Recovered(c, p), Cur(Recovered(c, p)))), TRUE)}
        BY DEF BuildRecovery
    <2>12. IsFiniteSet(proposals')
        BY ONLY FiniteInsert, <2>10, <2>11
    <2>9. UNCHANGED <<voteRequests, voteMessages, recoveryRequests, reportMessages, offers, ackMessages, confirmations, commitMessages>>
        BY DEF BuildRecovery
    <2> QED BY ONLY SMT, <2>0, <2>12, <2>9 DEF FiniteChannels

<1>2. FiniteNodeData'
    <2>0. FiniteMap(formal) /\ FiniteMap(stored) /\ FiniteMap(retained)
          /\ retained \in [Replicas -> SUBSET proposals]
        BY SMT DEF FiniteLogInvariant, FiniteNodeData, StorageShape, FiniteMap
    <2>1. FiniteMap(formal')
        BY SMT, <2>0 DEF BuildRecovery
    <2>2. FiniteMap(stored')
        <3>1. c \in Replicas /\ stored' = [stored EXCEPT ![c] = @ \cup {Entry(LastIndex(Recovered(c, p)) + 1, term[c], Cur(Recovered(c, p)) + 1,
                     NoValue, "noop", Count(Recovered(c, p), Cur(Recovered(c, p))))}]
            BY DEF BuildRecovery
        <3> QED BY ONLY FiniteMapInsert, <2>0, <3>1
    <2>3. FiniteMap(retained')
        BY SMT, <2>0 DEF BuildRecovery
    <2>4. retained' \in [Replicas -> SUBSET proposals']
        <3>1. retained' = retained /\ proposals \subseteq proposals'
            BY DEF BuildRecovery
        <3> QED BY ONLY SMT, <2>0, <3>1
    <2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF FiniteNodeData, StorageShape, FiniteMap

<1>3. FiniteProposals'
    <2>0. DEFINE added == Proposal(c, term[c], Recovered(c, p),
                Entry(LastIndex(Recovered(c, p)) + 1, term[c], Cur(Recovered(c, p)) + 1,
                      NoValue, "noop", Count(Recovered(c, p), Cur(Recovered(c, p)))), TRUE)
    <2>1. FiniteProposals /\ proposals' = proposals \cup {added}
        BY DEF FiniteLogInvariant, BuildRecovery, added
    <2>2. IsFiniteSet(Result(added))
        BY FiniteInsert, <1>0 DEF Result, Proposal, added
    <2> HIDE DEF added
    <2> QED BY ONLY ZenonT(5), <2>1, <2>2 DEF FiniteProposals

<1>4. FiniteSnapshots'
    BY ZenonT(10), FS_EmptySet, <1>0 DEF FiniteLogInvariant, FiniteSnapshots,
         FiniteNodeData, BuildRecovery
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF FiniteLogInvariant
=============================================================================
