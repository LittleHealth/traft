---------------------- MODULE TRaftPointCoreAliases05 ----------------------
EXTENDS TRaftPointCoreAliases04

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasMessageAckers ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : PointLift!MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY ZenonT(10)
   DEF MessageAckers, PointLift!MessageAckers

THEOREM PointCoreAliasAckers ==
    \A aliasArg1, aliasArg2, aliasArg3 : PointLift!Ackers(aliasArg1, aliasArg2, aliasArg3) = Ackers(aliasArg1, aliasArg2, aliasArg3)
BY ONLY ZenonT(10), PointCoreAliasMessageAckers
   DEF Ackers, PointLift!Ackers

THEOREM PointCoreAliasProposalAckers ==
    \A aliasArg1, aliasArg2 : PointLift!ProposalAckers(aliasArg1, aliasArg2) = ProposalAckers(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), PointCoreAliasResult, PointCoreAliasAck
   DEF ProposalAckers, PointLift!ProposalAckers

THEOREM PointCoreAliasPublish ==
    \A aliasArg1, aliasArg2 : PointLift!Publish(aliasArg1, aliasArg2) = Publish(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), PointCoreAliasResult
   DEF Publish, PointLift!Publish

THEOREM PointCoreAliasNormalMessage ==
    \A aliasArg1, aliasArg2 : PointLift!NormalMessage(aliasArg1, aliasArg2) = NormalMessage(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), PointCoreAliasCount
   DEF NormalMessage, PointLift!NormalMessage

THEOREM PointCoreAliasCanReceive ==
    \A aliasArg1, aliasArg2 : PointLift!CanReceive(aliasArg1, aliasArg2) = CanReceive(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), PointCoreAliasCur, PointCoreAliasCount, PointCoreAliasOrigin, PointCoreAliasAligned
   DEF CanReceive, PointLift!CanReceive

THEOREM PointCoreAliasInit ==
    PointLift!Init = Init
BY ONLY ZenonT(10), PointCoreAliasNoNode, PointCoreAliasNoProposal, PointCoreAliasEmptyReports
   DEF Init, PointLift!Init

THEOREM PointCoreAliasStartElection ==
    \A aliasArg1 : PointLift!StartElection(aliasArg1) = StartElection(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasNoProposal, PointCoreAliasTerms, PointCoreAliasEmptyReports
   DEF StartElection, PointLift!StartElection

THEOREM PointCoreAliasAdoptTerm ==
    \A aliasArg1, aliasArg2 : PointLift!AdoptTerm(aliasArg1, aliasArg2) = AdoptTerm(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasNoNode, PointCoreAliasNoProposal, PointCoreAliasEmptyReports
   DEF AdoptTerm, PointLift!AdoptTerm

THEOREM PointCoreAliasGrantVote ==
    \A aliasArg1, aliasArg2 : PointLift!GrantVote(aliasArg1, aliasArg2) = GrantVote(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasNoNode, PointCoreAliasRank, PointCoreAliasAtLeast
   DEF GrantVote, PointLift!GrantVote
=============================================================================
