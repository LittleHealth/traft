-------------------- MODULE TRaftUnboundedCoreAliases03 --------------------
EXTENDS TRaftUnboundedCoreAliases02

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasOrigin ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Origin(aliasArg1, aliasArg2) = Origin(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Origin, UnboundedCore!Origin, Part, UnboundedCore!Part

THEOREM UnboundedCoreAliasRank ==
    \A aliasArg1 : UnboundedCore!Rank(aliasArg1) = Rank(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasCur, UnboundedCoreAliasCount, UnboundedCoreAliasLastTerm
   DEF Rank, UnboundedCore!Rank

THEOREM UnboundedCoreAliasAtLeast ==
    \A aliasArg1, aliasArg2 : UnboundedCore!AtLeast(aliasArg1, aliasArg2) = AtLeast(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF AtLeast, UnboundedCore!AtLeast

THEOREM UnboundedCoreAliasQuorum ==
    \A aliasArg1 : UnboundedCore!Quorum(aliasArg1) = Quorum(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasCardinality
   DEF Quorum, UnboundedCore!Quorum

THEOREM UnboundedCoreAliasCoherent ==
    \A aliasArg1 : UnboundedCore!Coherent(aliasArg1) = Coherent(aliasArg1)
BY ONLY ZenonT(10)
   DEF Coherent, UnboundedCore!Coherent

THEOREM UnboundedCoreAliasEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6 : UnboundedCore!Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6) = Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6)
BY ONLY ZenonT(10)
   DEF Entry, UnboundedCore!Entry

THEOREM UnboundedCoreAliasProposal ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : UnboundedCore!Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Proposal, UnboundedCore!Proposal

THEOREM UnboundedCoreAliasResult ==
    \A aliasArg1 : UnboundedCore!Result(aliasArg1) = Result(aliasArg1)
BY ONLY ZenonT(10)
   DEF Result, UnboundedCore!Result

THEOREM UnboundedCoreAliasLater ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Later(aliasArg1, aliasArg2) = Later(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Later, UnboundedCore!Later

THEOREM UnboundedCoreAliasLatest ==
    \A aliasArg1 : UnboundedCore!Latest(aliasArg1) = Latest(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasLater
   DEF Latest, UnboundedCore!Latest
=============================================================================
