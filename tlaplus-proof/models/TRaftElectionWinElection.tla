------------------------- MODULE TRaftElectionWinElection -------------------------
EXTENDS TRaftElectionSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM WinElectionPreservesElection ==
    ASSUME ElectionInvariant, ObserveWinners, NEW c \in Replicas,
           WinElection(c)
    PROVE ElectionInvariant'
<1>1. voteMessages \subseteq voteMessages'
    BY SMT DEF WinElection
<1>2. BallotCertificates(winners, voteMessages')
    BY SMT, <1>1, BallotCertificatesGrow DEF ElectionInvariant, ElectionWinnerFacts
<1>3. Quorum(BallotVoters(voteMessages, term[c], c))
    BY WinningInboxHasCertificate
<1>31. winners' = winners \cup {[node |-> c, epoch |-> term[c]]}
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, ObserveWinners, WinElection
<1>32. BallotCertificates(winners', voteMessages')
    BY SMT, <1>3, <1>31, BallotCertificatesAdd
       DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, WinElection
<1>4. ElectionTypes'
    BY SMT DEF ElectionInvariant, ElectionTypes, WinElection, ElectionCoreVars, ElectionRequestFacts, ElectionBallotFacts, Roles
<1>5. ElectionRequestFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionRequestFacts, WinElection, ElectionCoreVars, ElectionBallotFacts
<1>6. ElectionBallotFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionBallotFacts, WinElection, ElectionCoreVars, ElectionRequestFacts
<1>7. ElectionInboxFacts'
    BY SMT DEF ElectionInvariant, ElectionTypes, ElectionInboxFacts, WinElection, ElectionCoreVars
<1>8. ElectionWinnerFacts'
    BY SMT, <1>31, <1>32 DEF ElectionInvariant, ElectionTypes, ElectionWinnerFacts, WinElection, ElectionCoreVars, ObserveWinners
<1> QED BY <1>4, <1>5, <1>6, <1>7, <1>8 DEF ElectionInvariant
=============================================================================
