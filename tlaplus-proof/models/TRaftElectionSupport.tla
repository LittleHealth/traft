------------------------- MODULE TRaftElectionSupport ------------------------
EXTENDS TRaftElectionState, TRaftQuorumProof, TLAPS
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM ElectionParameters ==
    /\ Terms \subseteq Nat /\ {0, 1} \subseteq Terms
    /\ IsFiniteSet(Replicas) /\ NoNode \notin Replicas
BY SMT DEF ParameterAssumptions

THEOREM StrictTermUpdateIsMonotone ==
    ASSUME NEW N, NEW before \in [N -> Nat], NEW r \in N,
           NEW t \in Nat, NEW after, after = [before EXCEPT ![r] = t],
           t > before[r]
    PROVE \A s \in N : before[s] <= after[s]
BY SMT

THEOREM BallotCertificatesGrow ==
    ASSUME NEW W, NEW M, NEW N, M \subseteq N, BallotCertificates(W, M)
    PROVE BallotCertificates(W, N)
<1>1. \A w \in W : BallotVoters(M, w.epoch, w.node) \subseteq BallotVoters(N, w.epoch, w.node)
    BY SMT DEF BallotVoters
<1>2. \A w \in W : Quorum(BallotVoters(N, w.epoch, w.node))
    <2>1. ASSUME NEW w \in W
          PROVE Quorum(BallotVoters(N, w.epoch, w.node))
        <3>1. Quorum(BallotVoters(M, w.epoch, w.node))
            BY SMT DEF BallotCertificates
        <3>2. BallotVoters(N, w.epoch, w.node) \subseteq Replicas
            BY SMT DEF BallotVoters
        <3>3. BallotVoters(M, w.epoch, w.node) \subseteq BallotVoters(N, w.epoch, w.node)
            BY <1>1
        <3> QED BY SMT, <3>1, <3>2, <3>3, MajorityUpward DEF Majority, Quorum
    <2> QED BY <2>1
<1> QED BY SMT, <1>2 DEF BallotCertificates

THEOREM BallotCertificatesAdd ==
    ASSUME NEW W, NEW M, BallotCertificates(W, M),
           NEW c \in Replicas, NEW t \in Terms \ {0},
           Quorum(BallotVoters(M, t, c))
    PROVE BallotCertificates(W \cup {[node |-> c, epoch |-> t]}, M)
BY SMT DEF BallotCertificates

THEOREM WinningInboxHasCertificate ==
    ASSUME ElectionInvariant, NEW c \in Replicas, WinElection(c)
    PROVE Quorum(BallotVoters(voteMessages, term[c], c))
<1>1. {m.sender : m \in {v \in voteInbox[c] : v.epoch = term[c]}}
          \subseteq BallotVoters(voteMessages, term[c], c)
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, ElectionBallotFacts, BallotVoters
<1>2. IsFiniteSet(Replicas)
    BY ElectionParameters
<1>3. BallotVoters(voteMessages, term[c], c) \subseteq Replicas
    BY SMT DEF BallotVoters
<1>4. Majority(Replicas, {m.sender : m \in {v \in voteInbox[c] : v.epoch = term[c]}})
    BY DEF WinElection, Majority, Quorum
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, MajorityUpward
    DEF Majority, Quorum

THEOREM ObservedWinnersAlreadyPresent ==
    ASSUME ObserveWinners,
           \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
               [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
    PROVE winners' = winners
<1>1. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
           [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
    OBVIOUS
<1>2. {[node |-> winnerNode, epoch |-> term'[winnerNode]] :
           winnerNode \in {candidateNode \in Replicas : role'[candidateNode] = "LeaderCandidate"}}
           \subseteq winners
    BY ONLY ZenonT(5), <1>1
<1> QED BY <1>2 DEF ObserveWinners

THEOREM ElectionInvariantInitially == Init => ElectionInvariant
BY SMT DEF Init, ElectionInvariant, ElectionTypes, ElectionRequestFacts,
           ElectionBallotFacts, ElectionInboxFacts, ElectionWinnerFacts,
           BallotCertificates, NoNode, Roles

THEOREM WinnerObservationProjection == Observe => ObserveWinners
BY SMT DEF Observe, ObserveWinners

THEOREM ElectionInvariantImpliesElectionSafety ==
    ASSUME ElectionInvariant
    PROVE ElectionSafety
<1>1. ASSUME NEW a \in winners, NEW b \in winners, a.epoch = b.epoch
      PROVE a.node = b.node
    <2>1. Quorum(BallotVoters(voteMessages, a.epoch, a.node))
          /\ Quorum(BallotVoters(voteMessages, b.epoch, b.node))
        BY SMT DEF ElectionInvariant, ElectionWinnerFacts, BallotCertificates
    <2>2. BallotVoters(voteMessages, a.epoch, a.node)
                 \cap BallotVoters(voteMessages, b.epoch, b.node) # {}
        BY SMT, <2>1, MajorityIntersection DEF Quorum, Majority
    <2> QED BY SMT, <1>1, <2>2 DEF BallotVoters, ElectionInvariant, ElectionBallotFacts
<1> QED BY <1>1 DEF ElectionSafety

THEOREM ElectionStuttering ==
    ASSUME ElectionInvariant, UNCHANGED ElectionVars
    PROVE ElectionInvariant'
BY SMT DEF ElectionInvariant, ElectionTypes, ElectionRequestFacts,
           ElectionBallotFacts, ElectionInboxFacts, ElectionWinnerFacts,
           ElectionVars, ElectionCoreVars

=============================================================================
