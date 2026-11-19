------------------------- MODULE TRaftElectionAdoptTerm -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM AdoptTermPreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW r \in Replicas, NEW t \in Terms,
           AdoptTerm(r, t)
    PROVE ElectionInvariant'
<1>0. term \in [Replicas -> Nat]
    BY SMT DEF ElectionInvariant, ElectionTypes, Terms
<1>02. t \in Nat
    BY SMT, ElectionParameters
<1>03. term' = [term EXCEPT ![r] = t] /\ t > term[r]
    BY DEF AdoptTerm
<1>01. \A s \in Replicas : term[s] <= term'[s]
    BY SMT, <1>0, <1>02, <1>03, StrictTermUpdateIsMonotone
<1>1. voteMessages \subseteq voteMessages'
    BY SMT DEF AdoptTerm
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
        BY SMT, <2>1 DEF AdoptTerm
    <2>3. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
        BY ONLY SMT, <2>1, <2>2
    <2> QED BY ObservedWinnersAlreadyPresent, <2>3
<1>4. ElectionTypes'
    BY SMT DEF ElectionInvariant, ElectionTypes, AdoptTerm, ElectionCoreVars, ElectionRequestFacts, ElectionBallotFacts, Roles
<1>5. ElectionRequestFacts'
    <2>1. ASSUME NEW req \in voteRequests
          PROVE req.candidate \in Replicas /\ req.epoch \in Terms \ {0}
                /\ req.epoch <= term'[req.candidate]
        <3>1. req.candidate \in Replicas /\ req.epoch \in Terms \ {0}
              /\ req.epoch <= term[req.candidate]
            BY SMT DEF ElectionInvariant, ElectionRequestFacts
        <3>2. req.epoch \in Nat /\ term[req.candidate] \in Nat
              /\ term'[req.candidate] \in Nat
            BY ONLY SMT, <3>1, <1>0, <1>4, ElectionParameters DEF ElectionTypes, Terms
        <3>3. term[req.candidate] <= term'[req.candidate]
            BY ONLY SMT, <3>1, <1>01
        <3> QED BY ONLY SMT, <3>1, <3>2, <3>3
    <2>2. \A req \in voteRequests' \ voteRequests :
          req.candidate \in Replicas /\ req.epoch \in Terms \ {0}
          /\ req.epoch <= term'[req.candidate]
        BY SMT, <1>0, ElectionParameters DEF AdoptTerm, ElectionInvariant, ElectionTypes, Terms
    <2> QED BY SMT, <2>1, <2>2 DEF ElectionRequestFacts
<1>6. ElectionBallotFacts'
<2>1. \A v \in voteMessages' : v.sender \in Replicas /\ v.receiver \in Replicas
             /\ v.epoch \in Terms \ {0}
    BY SMT, ElectionParameters, <1>0, <1>01, <1>4 DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, AdoptTerm, Terms
<2>2. ASSUME NEW v \in voteMessages'
      PROVE v.epoch <= term'[v.sender]
             /\ (v.epoch = term'[v.sender] => vote'[v.sender] = v.receiver)
    <3>1. term' = [term EXCEPT ![r] = t]
          /\ vote' = [vote EXCEPT ![r] = NoNode]
          /\ t > term[r]
          /\ voteMessages' = voteMessages
        BY SMT, <1>0 DEF AdoptTerm
    <3>2. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
          /\ vote \in [Replicas -> Replicas \cup {NoNode}]
          /\ r \in Replicas
        BY SMT, <1>0, <1>4, ElectionParameters DEF ElectionInvariant, ElectionTypes, Terms
    <3>3. CASE v \in voteMessages
        <4>1. v.sender \in Replicas /\ v.receiver \in Replicas
              /\ v.epoch \in Nat /\ v.epoch <= term[v.sender]
              /\ (v.epoch = term[v.sender] => vote[v.sender] = v.receiver)
            BY SMT, <3>3, ElectionParameters DEF ElectionInvariant, ElectionBallotFacts, Terms
        <4> QED BY ONLY SMT, <3>1, <3>2, <4>1
    <3>4. CASE v \notin voteMessages
        BY ONLY SMT, <2>2, <3>1, <3>2, <3>4
    <3> QED BY <3>3, <3>4
<2>3. \A v \in voteMessages' : \E req \in voteRequests' :
               req.candidate = v.receiver /\ req.epoch = v.epoch
    BY SMT, ElectionParameters, <1>0, <1>01, <1>4 DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, AdoptTerm, Terms
<2>4. \A a, b \in voteMessages' :
              a.sender = b.sender /\ a.epoch = b.epoch => a.receiver = b.receiver
    BY SMT, ElectionParameters, <1>0, <1>01, <1>4 DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, AdoptTerm, Terms
<2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF ElectionBallotFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, AdoptTerm, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    <2>1. BallotCertificates(winners', voteMessages')
        BY SMT, <1>2, <1>3
    <2>2. \A checkedReplica \in Replicas : role'[checkedReplica] \in {"LeaderCandidate", "Leader"} =>
              [node |-> checkedReplica, epoch |-> term'[checkedReplica]] \in winners'
        BY SMT, <1>3 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, AdoptTerm
    <2> QED BY <2>1, <2>2 DEF ElectionWinnerFacts
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
