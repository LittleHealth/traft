----------------------- MODULE TRaftLeaderHistoryProof ----------------------
EXTENDS TRaftLeaderHistoryFrames, TRaftElectionTemporal
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM LeaderHistoryInitially == Init => LeaderHistoryInvariant
BY SMT DEF Init, LeaderHistoryInvariant, PastLeaderViews, LeaderViewCertificates

THEOREM StartElectionPreservesPastLeaderViews ==
    ASSUME PastLeaderViews(leaderViews, term, role), ElectionTypes,
           NEW r \in Replicas, StartElection(r)
    PROVE PastLeaderViews(leaderViews, term', role')
BY SMT DEF StartElection, PastLeaderViews, ElectionTypes, Terms

THEOREM AdoptTermPreservesPastLeaderViews ==
    ASSUME PastLeaderViews(leaderViews, term, role), ElectionTypes,
           NEW r \in Replicas, NEW t \in Nat, AdoptTerm(r, t)
    PROVE PastLeaderViews(leaderViews, term', role')
BY SMT DEF AdoptTerm, PastLeaderViews, ElectionTypes, Terms

THEOREM WinElectionPreservesPastLeaderViews ==
    ASSUME PastLeaderViews(leaderViews, term, role), ElectionTypes,
           NEW r \in Replicas, WinElection(r)
    PROVE PastLeaderViews(leaderViews, term', role')
BY SMT DEF WinElection, PastLeaderViews, ElectionTypes, Terms

THEOREM ActivatePreservesPastLeaderViews ==
    ASSUME PastLeaderViews(leaderViews, term, role), ElectionTypes,
           NEW r \in Replicas, Activate(r)
    PROVE PastLeaderViews(leaderViews, term', role')
BY SMT DEF Activate, PastLeaderViews, ElectionTypes, Terms

THEOREM CrashPreservesPastLeaderViews ==
    ASSUME PastLeaderViews(leaderViews, term, role), ElectionTypes,
           NEW r \in Replicas, Crash(r)
    PROVE PastLeaderViews(leaderViews, term', role')
BY SMT DEF Crash, PastLeaderViews, ElectionTypes, Terms

THEOREM PastLeaderViewsFollowProtocol ==
    ASSUME LeaderHistoryInvariant, ElectionInvariant, ProtocolNext
    PROVE PastLeaderViews(leaderViews, term', role')
<1>1. LeaderControlChanges \/ UNCHANGED <<term, role>>
    BY LeaderControlProjection
<1>2. ElectionTypes /\ PastLeaderViews(leaderViews, term, role)
    BY DEF ElectionInvariant, LeaderHistoryInvariant
<1>3. \A r \in Replicas : \A t : AdoptTerm(r, t) => t \in Nat
    BY SMT DEF AdoptTerm, ElectionInvariant, ElectionRequestFacts, Terms
<1> QED BY SMT, <1>1, <1>2, <1>3, StartElectionPreservesPastLeaderViews,
    AdoptTermPreservesPastLeaderViews, WinElectionPreservesPastLeaderViews,
    ActivatePreservesPastLeaderViews, CrashPreservesPastLeaderViews
    DEF LeaderControlChanges

THEOREM ObservationPreservesLeaderHistory ==
    ASSUME LeaderHistoryInvariant, PastLeaderViews(leaderViews, term', role'),
           ElectionInvariant', Observe
    PROVE LeaderHistoryInvariant'
<1>1. leaderViews' = leaderViews \cup
          {[node |-> r, epoch |-> term'[r], entries |-> formal'[r]] :
           r \in {x \in Replicas : role'[x] = "Leader"}}
      /\ winners \subseteq winners'
    BY SMT DEF Observe
<1>2. \A r \in Replicas : role'[r] = "Leader" =>
           /\ term'[r] \in Terms \ {0}
           /\ [node |-> r, epoch |-> term'[r]] \in winners'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts
<1>20. PastLeaderViews(leaderViews, term', role')
      /\ LeaderViewCertificates(leaderViews, winners)
    BY DEF LeaderHistoryInvariant
<1>3. ASSUME NEW v \in leaderViews'
      PROVE /\ v.node \in Replicas /\ v.epoch \in Terms \ {0}
            /\ v.epoch <= term'[v.node]
            /\ (v.epoch = term'[v.node] => role'[v.node] \in {"Leader", "Follower"})
            /\ [node |-> v.node, epoch |-> v.epoch] \in winners'
    <2>1. CASE v \in leaderViews
        BY ONLY SMT, <1>1, <1>20, <2>1
           DEF PastLeaderViews, LeaderViewCertificates
    <2>2. CASE v \notin leaderViews
        <3>1. PICK r \in Replicas : role'[r] = "Leader"
                  /\ v = [node |-> r, epoch |-> term'[r], entries |-> formal'[r]]
            BY ONLY ZenonT(5), <1>1, <1>3, <2>2
        <3>2. term'[r] \in Terms \ {0}
              /\ [node |-> r, epoch |-> term'[r]] \in winners'
            BY ONLY <1>2, <3>1
        <3>3. term'[r] \in Nat
            BY ONLY SMT, <3>2 DEF Terms
        <3> QED BY ONLY SMT, <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2
<1> QED BY <1>3 DEF LeaderHistoryInvariant, PastLeaderViews, LeaderViewCertificates

THEOREM LeaderHistoryInductiveStep ==
    ASSUME LeaderHistoryInvariant, ElectionInvariant, Next
    PROVE LeaderHistoryInvariant'
<1>1. ElectionInvariant'
    BY ElectionInductiveStep
<1>2. PastLeaderViews(leaderViews, term', role')
    BY PastLeaderViewsFollowProtocol DEF Next
<1> QED BY ObservationPreservesLeaderHistory, <1>1, <1>2 DEF Next

THEOREM LeaderHistoryStuttering ==
    ASSUME LeaderHistoryInvariant, UNCHANGED vars
    PROVE LeaderHistoryInvariant'
BY SMT DEF LeaderHistoryInvariant, PastLeaderViews, LeaderViewCertificates,
    vars, protocolVars, observerVars

THEOREM ProtocolLeaderHistory == Spec => []LeaderHistoryInvariant
<1>1. Spec => []ElectionInvariant
    BY ElectionInvariantAlways
<1>2. Init => LeaderHistoryInvariant
    BY LeaderHistoryInitially
<1>3. LeaderHistoryInvariant /\ ElectionInvariant /\ [Next]_vars => LeaderHistoryInvariant'
    BY LeaderHistoryInductiveStep, LeaderHistoryStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
