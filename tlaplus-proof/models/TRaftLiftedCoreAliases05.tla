---------------------- MODULE TRaftLiftedCoreAliases05 ----------------------
EXTENDS TRaftLiftedCoreAliases04

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasMessageAckers ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : LiftedSafety!MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY ZenonT(10)
   DEF MessageAckers, LiftedSafety!MessageAckers

THEOREM LiftedCoreAliasAckers ==
    \A aliasArg1, aliasArg2, aliasArg3 : LiftedSafety!Ackers(aliasArg1, aliasArg2, aliasArg3) = Ackers(aliasArg1, aliasArg2, aliasArg3)
BY ONLY ZenonT(10), LiftedCoreAliasMessageAckers
   DEF Ackers, LiftedSafety!Ackers

THEOREM LiftedCoreAliasProposalAckers ==
    \A aliasArg1, aliasArg2 : LiftedSafety!ProposalAckers(aliasArg1, aliasArg2) = ProposalAckers(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), LiftedCoreAliasResult, LiftedCoreAliasAck
   DEF ProposalAckers, LiftedSafety!ProposalAckers

THEOREM LiftedCoreAliasPublish ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Publish(aliasArg1, aliasArg2) = Publish(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), LiftedCoreAliasResult
   DEF Publish, LiftedSafety!Publish

THEOREM LiftedCoreAliasNormalMessage ==
    \A aliasArg1, aliasArg2 : LiftedSafety!NormalMessage(aliasArg1, aliasArg2) = NormalMessage(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), LiftedCoreAliasCount
   DEF NormalMessage, LiftedSafety!NormalMessage

THEOREM LiftedCoreAliasCanReceive ==
    \A aliasArg1, aliasArg2 : LiftedSafety!CanReceive(aliasArg1, aliasArg2) = CanReceive(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), LiftedCoreAliasCur, LiftedCoreAliasCount, LiftedCoreAliasOrigin, LiftedCoreAliasAligned
   DEF CanReceive, LiftedSafety!CanReceive

THEOREM LiftedCoreAliasInit ==
    LiftedSafety!Init = Init
BY ONLY ZenonT(10), LiftedCoreAliasNoNode, LiftedCoreAliasNoProposal, LiftedCoreAliasEmptyReports
   DEF Init, LiftedSafety!Init

THEOREM LiftedCoreAliasStartElection ==
    \A aliasArg1 : LiftedSafety!StartElection(aliasArg1) = StartElection(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasNoProposal, LiftedCoreAliasTerms, LiftedCoreAliasEmptyReports
   DEF StartElection, LiftedSafety!StartElection

THEOREM LiftedCoreAliasAdoptTerm ==
    \A aliasArg1, aliasArg2 : LiftedSafety!AdoptTerm(aliasArg1, aliasArg2) = AdoptTerm(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasNoNode, LiftedCoreAliasNoProposal, LiftedCoreAliasEmptyReports
   DEF AdoptTerm, LiftedSafety!AdoptTerm

THEOREM LiftedCoreAliasGrantVote ==
    \A aliasArg1, aliasArg2 : LiftedSafety!GrantVote(aliasArg1, aliasArg2) = GrantVote(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasNoNode, LiftedCoreAliasRank, LiftedCoreAliasAtLeast
   DEF GrantVote, LiftedSafety!GrantVote
=============================================================================
