------------------------- MODULE TRaftElectionActivate -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM ActivatePreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW c \in Replicas,
           Activate(c)
    PROVE ElectionInvariant'
<1>1. voteMessages \subseteq voteMessages'
    BY SMT DEF Activate
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
        BY SMT, <2>1 DEF Activate
    <2>3. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
        BY ONLY SMT, <2>1, <2>2
    <2> QED BY ObservedWinnersAlreadyPresent, <2>3
<1>4. ElectionTypes'
    BY SMT DEF ElectionInvariant, ElectionTypes, Activate, ElectionCoreVars, ElectionRequestFacts, ElectionBallotFacts, Roles
<1>5. ElectionRequestFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionRequestFacts, Activate, ElectionCoreVars, ElectionBallotFacts
<1>6. ElectionBallotFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, Activate, ElectionCoreVars, ElectionRequestFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, Activate, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    BY SMT, <1>2, <1>3 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, Activate, ElectionCoreVars, ObserveWinners
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
