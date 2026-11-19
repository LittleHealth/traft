---------------------- MODULE TRaftPointCoreAliases03 ----------------------
EXTENDS TRaftPointCoreAliases02

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasOrigin ==
    \A aliasArg1, aliasArg2 : PointLift!Origin(aliasArg1, aliasArg2) = Origin(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Origin, PointLift!Origin, Part, PointLift!Part

THEOREM PointCoreAliasRank ==
    \A aliasArg1 : PointLift!Rank(aliasArg1) = Rank(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasCur, PointCoreAliasCount, PointCoreAliasLastTerm
   DEF Rank, PointLift!Rank

THEOREM PointCoreAliasAtLeast ==
    \A aliasArg1, aliasArg2 : PointLift!AtLeast(aliasArg1, aliasArg2) = AtLeast(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF AtLeast, PointLift!AtLeast

THEOREM PointCoreAliasQuorum ==
    \A aliasArg1 : PointLift!Quorum(aliasArg1) = Quorum(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasCardinality
   DEF Quorum, PointLift!Quorum

THEOREM PointCoreAliasCoherent ==
    \A aliasArg1 : PointLift!Coherent(aliasArg1) = Coherent(aliasArg1)
BY ONLY ZenonT(10)
   DEF Coherent, PointLift!Coherent

THEOREM PointCoreAliasEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6 : PointLift!Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6) = Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6)
BY ONLY ZenonT(10)
   DEF Entry, PointLift!Entry

THEOREM PointCoreAliasProposal ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : PointLift!Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Proposal, PointLift!Proposal

THEOREM PointCoreAliasResult ==
    \A aliasArg1 : PointLift!Result(aliasArg1) = Result(aliasArg1)
BY ONLY ZenonT(10)
   DEF Result, PointLift!Result

THEOREM PointCoreAliasLater ==
    \A aliasArg1, aliasArg2 : PointLift!Later(aliasArg1, aliasArg2) = Later(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Later, PointLift!Later

THEOREM PointCoreAliasLatest ==
    \A aliasArg1 : PointLift!Latest(aliasArg1) = Latest(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasLater
   DEF Latest, PointLift!Latest
=============================================================================
