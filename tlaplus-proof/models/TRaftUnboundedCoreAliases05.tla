-------------------- MODULE TRaftUnboundedCoreAliases05 --------------------
EXTENDS TRaftUnboundedCoreAliases04

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasMessageAckers ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : UnboundedCore!MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY ZenonT(10)
   DEF MessageAckers, UnboundedCore!MessageAckers

THEOREM UnboundedCoreAliasAckers ==
    \A aliasArg1, aliasArg2, aliasArg3 : UnboundedCore!Ackers(aliasArg1, aliasArg2, aliasArg3) = Ackers(aliasArg1, aliasArg2, aliasArg3)
BY ONLY ZenonT(10), UnboundedCoreAliasMessageAckers
   DEF Ackers, UnboundedCore!Ackers

THEOREM UnboundedCoreAliasProposalAckers ==
    \A aliasArg1, aliasArg2 : UnboundedCore!ProposalAckers(aliasArg1, aliasArg2) = ProposalAckers(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedCoreAliasResult, UnboundedCoreAliasAck
   DEF ProposalAckers, UnboundedCore!ProposalAckers

THEOREM UnboundedCoreAliasPublish ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Publish(aliasArg1, aliasArg2) = Publish(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedCoreAliasResult
   DEF Publish, UnboundedCore!Publish

THEOREM UnboundedCoreAliasNormalMessage ==
    \A aliasArg1, aliasArg2 : UnboundedCore!NormalMessage(aliasArg1, aliasArg2) = NormalMessage(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedCoreAliasCount
   DEF NormalMessage, UnboundedCore!NormalMessage

THEOREM UnboundedCoreAliasCanReceive ==
    \A aliasArg1, aliasArg2 : UnboundedCore!CanReceive(aliasArg1, aliasArg2) = CanReceive(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedConstantSelections, UnboundedCoreAliasCur, UnboundedCoreAliasCount, UnboundedCoreAliasOrigin, UnboundedCoreAliasAligned
   DEF CanReceive, UnboundedCore!CanReceive

THEOREM UnboundedCoreAliasInit ==
    UnboundedCore!Init = Init
BY ONLY ZenonT(10), UnboundedCoreAliasNoNode, UnboundedCoreAliasNoProposal, UnboundedCoreAliasEmptyReports
   DEF Init, UnboundedCore!Init

THEOREM UnboundedCoreAliasStartElection ==
    \A aliasArg1 : UnboundedCore!StartElection(aliasArg1) = StartElection(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasNoProposal, UnboundedCoreAliasTerms, UnboundedCoreAliasEmptyReports
   DEF StartElection, UnboundedCore!StartElection

THEOREM UnboundedCoreAliasAdoptTerm ==
    \A aliasArg1, aliasArg2 : UnboundedCore!AdoptTerm(aliasArg1, aliasArg2) = AdoptTerm(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasNoNode, UnboundedCoreAliasNoProposal, UnboundedCoreAliasEmptyReports
   DEF AdoptTerm, UnboundedCore!AdoptTerm

THEOREM UnboundedCoreAliasGrantVote ==
    \A aliasArg1, aliasArg2 : UnboundedCore!GrantVote(aliasArg1, aliasArg2) = GrantVote(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasNoNode, UnboundedCoreAliasRank, UnboundedCoreAliasAtLeast
   DEF GrantVote, UnboundedCore!GrantVote
=============================================================================
