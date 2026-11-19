---------------------- MODULE TRaftPointCoreAliases02 ----------------------
EXTENDS TRaftPointCoreAliases01

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasEntries ==
    PointLift!Entries = Entries
BY ONLY ZenonT(10), PointCoreAliasTerms, PointCoreAliasIndices, PointCoreAliasPartitions
   DEF Entries, PointLift!Entries

THEOREM PointCoreAliasProposalRecords ==
    PointLift!ProposalRecords = ProposalRecords
BY ONLY ZenonT(10), PointCoreAliasTerms, PointCoreAliasEntries
   DEF ProposalRecords, PointLift!ProposalRecords

THEOREM PointCoreAliasMaxOr ==
    \A aliasArg1, aliasArg2 : PointLift!MaxOr(aliasArg1, aliasArg2) = MaxOr(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF MaxOr, PointLift!MaxOr

THEOREM PointCoreAliasCur ==
    \A aliasArg1 : PointLift!Cur(aliasArg1) = Cur(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasMaxOr
   DEF Cur, PointLift!Cur

THEOREM PointCoreAliasLastIndex ==
    \A aliasArg1 : PointLift!LastIndex(aliasArg1) = LastIndex(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasMaxOr
   DEF LastIndex, PointLift!LastIndex

THEOREM PointCoreAliasPart ==
    \A aliasArg1, aliasArg2 : PointLift!Part(aliasArg1, aliasArg2) = Part(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Part, PointLift!Part

THEOREM PointCoreAliasPrefix ==
    \A aliasArg1, aliasArg2 : PointLift!Prefix(aliasArg1, aliasArg2) = Prefix(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Prefix, PointLift!Prefix

THEOREM PointCoreAliasCount ==
    \A aliasArg1, aliasArg2 : PointLift!Count(aliasArg1, aliasArg2) = Count(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), PointCoreAliasCardinality, PointCoreAliasPart
   DEF Count, PointLift!Count

THEOREM PointCoreAliasClosedPrefix ==
    \A aliasArg1 : PointLift!ClosedPrefix(aliasArg1) = ClosedPrefix(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasCur, PointCoreAliasPrefix
   DEF ClosedPrefix, PointLift!ClosedPrefix

THEOREM PointCoreAliasLastTerm ==
    \A aliasArg1 : PointLift!LastTerm(aliasArg1) = LastTerm(aliasArg1)
BY ONLY ZenonT(10)
   DEF LastTerm, PointLift!LastTerm, LastIndex, PointLift!LastIndex,
       MaxOr, PointLift!MaxOr
=============================================================================
