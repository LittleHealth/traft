-------------------- MODULE TRaftUnboundedClientCoreAliases05 --------------------
EXTENDS TRaftUnboundedClientCoreAliases04

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasMessageAckers ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : UnboundedClient!MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = MessageAckers(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY ZenonT(10)
   DEF MessageAckers, UnboundedClient!MessageAckers

THEOREM UnboundedClientCoreAliasAckers ==
    \A aliasArg1, aliasArg2, aliasArg3 : UnboundedClient!Ackers(aliasArg1, aliasArg2, aliasArg3) = Ackers(aliasArg1, aliasArg2, aliasArg3)
BY ONLY ZenonT(10), UnboundedClientCoreAliasMessageAckers
   DEF Ackers, UnboundedClient!Ackers

THEOREM UnboundedClientCoreAliasProposalAckers ==
    \A aliasArg1, aliasArg2 : UnboundedClient!ProposalAckers(aliasArg1, aliasArg2) = ProposalAckers(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedClientCoreAliasResult, UnboundedClientCoreAliasAck
   DEF ProposalAckers, UnboundedClient!ProposalAckers

THEOREM UnboundedClientCoreAliasPublish ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Publish(aliasArg1, aliasArg2) = Publish(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedClientCoreAliasResult
   DEF Publish, UnboundedClient!Publish

THEOREM UnboundedClientCoreAliasNormalMessage ==
    \A aliasArg1, aliasArg2 : UnboundedClient!NormalMessage(aliasArg1, aliasArg2) = NormalMessage(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedClientCoreAliasCount
   DEF NormalMessage, UnboundedClient!NormalMessage

THEOREM UnboundedClientCoreAliasCanReceive ==
    \A aliasArg1, aliasArg2 : UnboundedClient!CanReceive(aliasArg1, aliasArg2) = CanReceive(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientConstantSelections, UnboundedClientCoreAliasCur, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasOrigin, UnboundedClientCoreAliasAligned
   DEF CanReceive, UnboundedClient!CanReceive

THEOREM UnboundedClientCoreAliasInit ==
    UnboundedClient!Init = Init
BY ONLY ZenonT(10), UnboundedClientCoreAliasNoNode, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasEmptyReports
   DEF Init, UnboundedClient!Init

THEOREM UnboundedClientCoreAliasStartElection ==
    \A aliasArg1 : UnboundedClient!StartElection(aliasArg1) = StartElection(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasEmptyReports
   DEF StartElection, UnboundedClient!StartElection

THEOREM UnboundedClientCoreAliasAdoptTerm ==
    \A aliasArg1, aliasArg2 : UnboundedClient!AdoptTerm(aliasArg1, aliasArg2) = AdoptTerm(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasNoNode, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasEmptyReports
   DEF AdoptTerm, UnboundedClient!AdoptTerm

THEOREM UnboundedClientCoreAliasGrantVote ==
    \A aliasArg1, aliasArg2 : UnboundedClient!GrantVote(aliasArg1, aliasArg2) = GrantVote(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasNoNode, UnboundedClientCoreAliasRank, UnboundedClientCoreAliasAtLeast
   DEF GrantVote, UnboundedClient!GrantVote
=============================================================================
