------------------------- MODULE TRaftElectionCrash -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM CrashPreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW c \in Replicas,
           Crash(c)
    PROVE ElectionInvariant'
<1>1. voteMessages \subseteq voteMessages'
    BY SMT DEF Crash
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
        BY SMT, <2>1 DEF Crash
    <2>3. \A winnerNode \in Replicas : role'[winnerNode] = "LeaderCandidate" =>
              [node |-> winnerNode, epoch |-> term'[winnerNode]] \in winners
        BY ONLY SMT, <2>1, <2>2
    <2> QED BY ObservedWinnersAlreadyPresent, <2>3
<1>4. ElectionTypes'
    BY SMT DEF ElectionInvariant, ElectionTypes, Crash, ElectionCoreVars, ElectionRequestFacts, ElectionBallotFacts, Roles
<1>5. ElectionRequestFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionRequestFacts, Crash, ElectionCoreVars, ElectionBallotFacts
<1>6. ElectionBallotFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, Crash, ElectionCoreVars, ElectionRequestFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, Crash, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    <2>1. BallotCertificates(winners', voteMessages')
        BY SMT, <1>2, <1>3
    <2>2. \A r \in Replicas : role'[r] \in {"LeaderCandidate", "Leader"} =>
              [node |-> r, epoch |-> term'[r]] \in winners'
        BY SMT, <1>3 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, Crash
    <2> QED BY <2>1, <2>2 DEF ElectionWinnerFacts
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
