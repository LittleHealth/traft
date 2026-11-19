------------------------- MODULE TRaftElectionGrantVote -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM GrantVotePreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW r \in Replicas, NEW req \in voteRequests,
           GrantVote(r, req)
    PROVE ElectionInvariant'
<1>1. voteMessages \subseteq voteMessages'
    BY SMT DEF GrantVote
<1>2. BallotCertificates(winners, voteMessages')
    BY SMT, <1>1, BallotCertificatesGrow DEF ElectionInvariant, ElectionWinnerFacts
<1>3. winners' = winners
    <2>1. term \in [Replicas -> Terms] /\ role \in [Replicas -> Roles]
          /\ \A oldNode \in Replicas : role[oldNode] \in {"LeaderCandidate", "Leader"} =>
                [node |-> oldNode, epoch |-> term[oldNode]] \in winners
        BY DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts
    <2>2. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              term'[winnerNode] = term[winnerNode]
              /\ role[winnerNode] \in {"LeaderCandidate", "Leader"}
        BY SMT, <2>1 DEF GrantVote
    <2>3. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
        BY ONLY SMT, <2>1, <2>2
    <2> QED BY ObservedWinnersAlreadyPresent, <2>3
<1>4. ElectionTypes'
    BY SMT DEF ElectionInvariant, ElectionTypes, GrantVote, ElectionCoreVars, ElectionRequestFacts, ElectionBallotFacts, Roles
<1>5. ElectionRequestFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionRequestFacts, GrantVote, ElectionCoreVars, ElectionBallotFacts
<1>6. ElectionBallotFacts'
<2>1. \A v \in voteMessages' : v.sender \in Replicas /\ v.receiver \in Replicas
             /\ v.epoch \in Terms \ {0}
    BY SMT, ElectionParameters DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, GrantVote, Terms
<2>2. ASSUME NEW v \in voteMessages'
      PROVE v.epoch <= term'[v.sender]
             /\ (v.epoch = term'[v.sender] => vote'[v.sender] = v.receiver)
    <3>1. term' = term /\ vote' = [vote EXCEPT ![r] = req.candidate]
          /\ term[r] = req.epoch /\ vote[r] \in {NoNode, req.candidate}
          /\ voteMessages' = voteMessages \cup
                  {[sender |-> r, receiver |-> req.candidate, epoch |-> req.epoch]}
        BY DEF GrantVote
    <3>2. r \in Replicas /\ term \in [Replicas -> Nat]
          /\ vote \in [Replicas -> Replicas \cup {NoNode}]
        BY SMT, ElectionParameters DEF ElectionInvariant, ElectionTypes, Terms
    <3>3. CASE v \in voteMessages
        <4>1. v.sender \in Replicas /\ v.receiver \in Replicas
              /\ v.epoch \in Nat /\ v.epoch <= term[v.sender]
              /\ (v.epoch = term[v.sender] => vote[v.sender] = v.receiver)
            BY SMT, <3>3, ElectionParameters DEF ElectionInvariant, ElectionBallotFacts, Terms
        <4> QED BY ONLY SMT, <3>1, <3>2, <4>1, ElectionParameters
    <3>4. CASE v \notin voteMessages
        BY ONLY SMT, <2>2, <3>1, <3>2, <3>4
    <3> QED BY <3>3, <3>4
<2>3. \A v \in voteMessages' : \E ballotRequest \in voteRequests' :
               ballotRequest.candidate = v.receiver /\ ballotRequest.epoch = v.epoch
    BY SMT, ElectionParameters DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, GrantVote, Terms
<2>4. \A a, b \in voteMessages' :
              a.sender = b.sender /\ a.epoch = b.epoch => a.receiver = b.receiver
    BY SMT, ElectionParameters DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, GrantVote, Terms
<2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF ElectionBallotFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, GrantVote, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    <2>1. BallotCertificates(winners', voteMessages')
        BY SMT, <1>2, <1>3
    <2>2. \A checkedReplica \in Replicas : role'[checkedReplica] \in {"LeaderCandidate", "Leader"} =>
              [node |-> checkedReplica, epoch |-> term'[checkedReplica]] \in winners'
        BY SMT, <1>3 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, GrantVote
    <2> QED BY <2>1, <2>2 DEF ElectionWinnerFacts
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
