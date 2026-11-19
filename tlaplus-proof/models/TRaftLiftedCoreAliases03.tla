---------------------- MODULE TRaftLiftedCoreAliases03 ----------------------
EXTENDS TRaftLiftedCoreAliases02

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasOrigin ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Origin(aliasArg1, aliasArg2) = Origin(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Origin, LiftedSafety!Origin, Part, LiftedSafety!Part

THEOREM LiftedCoreAliasRank ==
    \A aliasArg1 : LiftedSafety!Rank(aliasArg1) = Rank(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasCur, LiftedCoreAliasCount, LiftedCoreAliasLastTerm
   DEF Rank, LiftedSafety!Rank

THEOREM LiftedCoreAliasAtLeast ==
    \A aliasArg1, aliasArg2 : LiftedSafety!AtLeast(aliasArg1, aliasArg2) = AtLeast(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF AtLeast, LiftedSafety!AtLeast

THEOREM LiftedCoreAliasQuorum ==
    \A aliasArg1 : LiftedSafety!Quorum(aliasArg1) = Quorum(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasCardinality
   DEF Quorum, LiftedSafety!Quorum

THEOREM LiftedCoreAliasCoherent ==
    \A aliasArg1 : LiftedSafety!Coherent(aliasArg1) = Coherent(aliasArg1)
BY ONLY ZenonT(10)
   DEF Coherent, LiftedSafety!Coherent

THEOREM LiftedCoreAliasEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6 : LiftedSafety!Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6) = Entry(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5, aliasArg6)
BY ONLY ZenonT(10)
   DEF Entry, LiftedSafety!Entry

THEOREM LiftedCoreAliasProposal ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : LiftedSafety!Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Proposal(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Proposal, LiftedSafety!Proposal

THEOREM LiftedCoreAliasResult ==
    \A aliasArg1 : LiftedSafety!Result(aliasArg1) = Result(aliasArg1)
BY ONLY ZenonT(10)
   DEF Result, LiftedSafety!Result

THEOREM LiftedCoreAliasLater ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Later(aliasArg1, aliasArg2) = Later(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Later, LiftedSafety!Later

THEOREM LiftedCoreAliasLatest ==
    \A aliasArg1 : LiftedSafety!Latest(aliasArg1) = Latest(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasLater
   DEF Latest, LiftedSafety!Latest
=============================================================================
