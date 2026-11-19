-------------------------- MODULE TRaftElectionState -------------------------
EXTENDS TRaftCore

\* Auxiliary predicates only. No protocol action reads these predicates.
ElectionCoreVars == <<term, vote, role, voteRequests, voteMessages, voteInbox>>
ElectionVars == <<ElectionCoreVars, winners>>

BallotVoters(M, t, c) == {r \in Replicas : \E v \in M :
                           v.sender = r /\ v.receiver = c /\ v.epoch = t}
BallotCertificates(W, M) ==
    /\ W \subseteq [node : Replicas, epoch : Terms \ {0}]
    /\ \A w \in W : Quorum(BallotVoters(M, w.epoch, w.node))

ElectionTypes ==
    /\ term \in [Replicas -> Terms]
    /\ vote \in [Replicas -> Replicas \cup {NoNode}]
    /\ role \in [Replicas -> Roles]
    /\ voteInbox \in [Replicas -> SUBSET voteMessages]
    /\ \A r \in Replicas : role[r] # "Follower" => term[r] \in Terms \ {0}

ElectionRequestFacts == \A req \in voteRequests :
    /\ req.candidate \in Replicas /\ req.epoch \in Terms \ {0}
    /\ req.epoch <= term[req.candidate]

ElectionBallotFacts ==
    /\ \A v \in voteMessages :
         /\ v.sender \in Replicas /\ v.receiver \in Replicas
         /\ v.epoch \in Terms \ {0} /\ v.epoch <= term[v.sender]
         /\ v.epoch = term[v.sender] => vote[v.sender] = v.receiver
         /\ \E req \in voteRequests : req.candidate = v.receiver /\ req.epoch = v.epoch
    /\ \A a, b \in voteMessages :
         a.sender = b.sender /\ a.epoch = b.epoch => a.receiver = b.receiver

ElectionInboxFacts == \A r \in Replicas : \A v \in voteInbox[r] :
                        v.receiver = r /\ v.epoch = term[r]

ElectionWinnerFacts ==
    /\ BallotCertificates(winners, voteMessages)
    /\ \A r \in Replicas : role[r] \in {"LeaderCandidate", "Leader"} =>
          [node |-> r, epoch |-> term[r]] \in winners

ElectionInvariant == /\ ElectionTypes /\ ElectionRequestFacts
                     /\ ElectionBallotFacts /\ ElectionInboxFacts
                     /\ ElectionWinnerFacts

ObserveWinners == winners' = winners \cup
    {[node |-> r, epoch |-> term'[r]] :
        r \in {x \in Replicas : role'[x] = "LeaderCandidate"}}

ElectionChangingNext ==
    \/ \E c \in Replicas : StartElection(c) \/ WinElection(c) \/ Activate(c) \/ Crash(c)
    \/ \E r \in Replicas, t \in Terms : AdoptTerm(r, t)
    \/ \E r \in Replicas, req \in voteRequests : GrantVote(r, req)
    \/ \E c \in Replicas, m \in voteMessages : DeliverVote(c, m)
=============================================================================
