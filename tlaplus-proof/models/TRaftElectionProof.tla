-------------------------- MODULE TRaftElectionProof -------------------------
EXTENDS TRaftProofState, TRaftQuorumProof, TLAPS
USE ParameterAssumptions DEF ParameterAssumptions

Voters(t, c) == {r \in Replicas : \E v \in voteMessages :
                     v.sender = r /\ v.receiver = c /\ v.epoch = t}

THEOREM WinnerHasVoterQuorum ==
    ASSUME TermAndVoteFacts, NEW w \in winners
    PROVE Quorum(Voters(w.epoch, w.node))
<1>1. Voters(w.epoch, w.node) =
       {v.sender : v \in {a \in voteMessages : a.epoch = w.epoch /\ a.receiver = w.node}}
    BY SMT DEF TermAndVoteFacts, Voters
<1> QED BY SMT, <1>1 DEF TermAndVoteFacts

THEOREM OneVoteAndQuorumsGiveElectionSafety ==
    ASSUME TermAndVoteFacts
    PROVE ElectionSafety
<1>1. ASSUME NEW a \in winners, NEW b \in winners, a.epoch = b.epoch
      PROVE a.node = b.node
    <2>1. Quorum(Voters(a.epoch, a.node)) /\ Quorum(Voters(b.epoch, b.node))
        BY SMT, WinnerHasVoterQuorum
    <2>2. Voters(a.epoch, a.node) \cap Voters(b.epoch, b.node) # {}
        BY SMT, <2>1, MajorityIntersection DEF Quorum, Majority
    <2> QED BY SMT, <1>1, <2>2 DEF Voters, TermAndVoteFacts
<1> QED BY <1>1 DEF ElectionSafety

=============================================================================
