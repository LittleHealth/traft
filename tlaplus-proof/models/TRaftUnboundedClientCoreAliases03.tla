-------------------- MODULE TRaftUnboundedClientCoreAliases03 --------------------
EXTENDS TRaftUnboundedClientCoreAliases02

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasOrigin ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Origin(aliasArg1, aliasArg2) = Origin(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Origin, UnboundedClient!Origin, Part, UnboundedClient!Part

THEOREM UnboundedClientCoreAliasRank ==
    \A aliasArg1 : UnboundedClient!Rank(aliasArg1) = Rank(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasCur, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasLastTerm
   DEF Rank, UnboundedClient!Rank

THEOREM UnboundedClientCoreAliasAtLeast ==
    \A aliasArg1, aliasArg2 : UnboundedClient!AtLeast(aliasArg1, aliasArg2) = AtLeast(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF AtLeast, UnboundedClient!AtLeast

THEOREM UnboundedClientCoreAliasQuorum ==
    \A aliasArg1 : UnboundedClient!Quorum(aliasArg1) = Quorum(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasCardinality
   DEF Quorum, UnboundedClient!Quorum

THEOREM UnboundedClientCoreAliasCoherent ==
    \A aliasArg1 : UnboundedClient!Coherent(aliasArg1) = Coherent(aliasArg1)
BY ONLY ZenonT(10)
   DEF Coherent, UnboundedClient!Coherent

THEOREM UnboundedClientCoreAliasEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6 : UnboundedClient!Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6) = Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6)
BY ONLY ZenonT(10)
   DEF Entry, UnboundedClient!Entry

THEOREM UnboundedClientCoreAliasProposal ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : UnboundedClient!Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Proposal, UnboundedClient!Proposal

THEOREM UnboundedClientCoreAliasResult ==
    \A aliasArg1 : UnboundedClient!Result(aliasArg1) = Result(aliasArg1)
BY ONLY ZenonT(10)
   DEF Result, UnboundedClient!Result

THEOREM UnboundedClientCoreAliasLater ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Later(aliasArg1, aliasArg2) = Later(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Later, UnboundedClient!Later

THEOREM UnboundedClientCoreAliasLatest ==
    \A aliasArg1 : UnboundedClient!Latest(aliasArg1) = Latest(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasLater
   DEF Latest, UnboundedClient!Latest
=============================================================================
