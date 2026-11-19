------------------------- MODULE TRaftElectionStartElection -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM StartElectionPreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW c \in Replicas,
           StartElection(c)
    PROVE ElectionInvariant'
<1>00. ElectionInvariant /\ ObserveWinners /\ c \in Replicas /\ StartElection(c)
    OBVIOUS
<1>02. term' = [term EXCEPT ![c] = term[c] + 1]
       /\ vote' = [vote EXCEPT ![c] = c]
       /\ role' = [role EXCEPT ![c] = "Candidate"]
       /\ voteMessages' = voteMessages \cup
            {[sender |-> c, receiver |-> c, epoch |-> term[c] + 1]}
    BY ONLY <1>00 DEF StartElection
<1>03. term \in [Replicas -> Terms] /\ term[c] + 1 \in Terms /\ c \in Replicas
    BY ONLY <1>00 DEF ElectionInvariant, ElectionTypes, StartElection
<1>0. term \in [Replicas -> Nat]
    BY SMT DEF ElectionInvariant, ElectionTypes, Terms
<1>01. \A r \in Replicas : term[r] <= term'[r]
    BY SMT, <1>0 DEF StartElection
<1>1. voteMessages \subseteq voteMessages'
    BY ONLY <1>02
<1>2. BallotCertificates(winners, voteMessages')
    BY SMT, <1>1, BallotCertificatesGrow DEF ElectionInvariant, ElectionWinnerFacts
<1>3. winners' = winners
    <2>1. role \in [Replicas -> Roles]
          /\ \A r \in Replicas : role[r] \in {"LeaderCandidate", "Leader"} =>
                [node |-> r, epoch |-> term[r]] \in winners
        BY ONLY <1>00 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts
    <2>2. \A r \in Replicas : role'[r] = "LeaderCandidate" =>
              r # c /\ role'[r] = role[r] /\ term'[r] = term[r]
        BY ONLY SMT, <1>02, <1>03, <2>1
    <2>3. {[node |-> r, epoch |-> term'[r]] :
               r \in {x \in Replicas : role'[x] = "LeaderCandidate"}} \subseteq winners
        BY ONLY ZenonT(10), <2>1, <2>2
    <2> QED BY ONLY <1>00, <2>3 DEF ObserveWinners
<1>4. ElectionTypes'
    <2>1. term' \in [Replicas -> Terms]
        BY ONLY SMT, <1>02, <1>03
    <2>2. vote' \in [Replicas -> Replicas \cup {NoNode}]
        BY SMT DEF ElectionInvariant, ElectionTypes, StartElection
    <2>3. role' \in [Replicas -> Roles]
        BY SMT DEF ElectionInvariant, ElectionTypes, StartElection, Roles
    <2>4. voteInbox' \in [Replicas -> SUBSET voteMessages']
        BY SMT, <1>1 DEF ElectionInvariant, ElectionTypes, StartElection
    <2>5. \A r \in Replicas : role'[r] # "Follower" => term'[r] \in Terms \ {0}
        BY SMT, <1>0 DEF ElectionInvariant, ElectionTypes, StartElection
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF ElectionTypes
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
        BY SMT, <1>0, ElectionParameters DEF StartElection, ElectionInvariant, ElectionTypes, Terms
    <2> QED BY SMT, <2>1, <2>2 DEF ElectionRequestFacts
<1>6. ElectionBallotFacts'
<2>1. \A v \in voteMessages' : v.sender \in Replicas /\ v.receiver \in Replicas
             /\ v.epoch \in Terms \ {0}
    BY SMT, ElectionParameters, <1>0, <1>01, <1>4 DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, StartElection, Terms
<2>2. ASSUME NEW v \in voteMessages'
      PROVE v.epoch <= term'[v.sender]
             /\ (v.epoch = term'[v.sender] => vote'[v.sender] = v.receiver)
    <3>1. term' = [term EXCEPT ![c] = term[c] + 1]
          /\ vote' = [vote EXCEPT ![c] = c]
          /\ term[c] + 1 > term[c]
          /\ voteMessages' = voteMessages \cup {[sender |-> c, receiver |-> c, epoch |-> term[c] + 1]}
        BY ONLY SMT, <1>0, <1>02, <1>03
    <3>2. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
          /\ vote \in [Replicas -> Replicas \cup {NoNode}]
          /\ c \in Replicas
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
<2>3. ASSUME NEW v \in voteMessages'
      PROVE \E req \in voteRequests' :
               req.candidate = v.receiver /\ req.epoch = v.epoch
    <3>1. \A oldVote \in voteMessages : \E req \in voteRequests :
                req.candidate = oldVote.receiver /\ req.epoch = oldVote.epoch
        BY SMT DEF ElectionInvariant, ElectionBallotFacts
    <3>2. voteMessages' = voteMessages \cup
                  {[sender |-> c, receiver |-> c, epoch |-> term[c] + 1]}
          /\ voteRequests' = voteRequests \cup
                  {[candidate |-> c, epoch |-> term[c] + 1, entries |-> formal[c]]}
        BY DEF StartElection
    <3>3. CASE v \in voteMessages
        <4>1. PICK req \in voteRequests :
                  req.candidate = v.receiver /\ req.epoch = v.epoch
            BY ONLY <3>1, <3>3
        <4> QED BY ONLY SMT, <3>2, <4>1
    <3>4. CASE v \notin voteMessages
        <4>1. v = [sender |-> c, receiver |-> c, epoch |-> term[c] + 1]
            BY ONLY SMT, <2>3, <3>2, <3>4
        <4>2. [candidate |-> c, epoch |-> term[c] + 1, entries |-> formal[c]]
                  \in voteRequests'
            BY ONLY SMT, <3>2
        <4> QED BY ONLY SMT, <4>1, <4>2
    <3> QED BY <3>3, <3>4
<2>4. \A a, b \in voteMessages' :
              a.sender = b.sender /\ a.epoch = b.epoch => a.receiver = b.receiver
    BY SMT, ElectionParameters, <1>0, <1>01, <1>4 DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, ElectionRequestFacts, StartElection, Terms
<2> QED BY SMT, <2>1, <2>2, <2>3, <2>4 DEF ElectionBallotFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, StartElection, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    <2>1. BallotCertificates(winners', voteMessages')
        BY SMT, <1>2, <1>3
    <2>2. \A r \in Replicas : role'[r] \in {"LeaderCandidate", "Leader"} =>
              [node |-> r, epoch |-> term'[r]] \in winners'
        BY SMT, <1>3 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, StartElection
    <2> QED BY <2>1, <2>2 DEF ElectionWinnerFacts
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
