----------------------- MODULE TRaftLeaderHistoryState ----------------------
EXTENDS TRaftCore

PastLeaderViews(V, T, R) == \A v \in V :
    /\ v.node \in Replicas /\ v.epoch \in Terms \ {0}
    /\ v.epoch <= T[v.node]
    /\ v.epoch = T[v.node] => R[v.node] \in {"Leader", "Follower"}
LeaderViewCertificates(V, W) == \A v \in V :
    [node |-> v.node, epoch |-> v.epoch] \in W
LeaderHistoryInvariant ==
    /\ PastLeaderViews(leaderViews, term, role)
    /\ LeaderViewCertificates(leaderViews, winners)
=============================================================================
