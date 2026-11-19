---------------------- MODULE TRaftLiftedCoreAliases02 ----------------------
EXTENDS TRaftLiftedCoreAliases01

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasEntries ==
    LiftedSafety!Entries = Entries
BY ONLY ZenonT(10), LiftedCoreAliasTerms, LiftedCoreAliasIndices, LiftedCoreAliasPartitions
   DEF Entries, LiftedSafety!Entries

THEOREM LiftedCoreAliasProposalRecords ==
    LiftedSafety!ProposalRecords = ProposalRecords
BY ONLY ZenonT(10), LiftedCoreAliasTerms, LiftedCoreAliasEntries
   DEF ProposalRecords, LiftedSafety!ProposalRecords

THEOREM LiftedCoreAliasMaxOr ==
    \A aliasArg1, aliasArg2 : LiftedSafety!MaxOr(aliasArg1, aliasArg2) = MaxOr(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF MaxOr, LiftedSafety!MaxOr

THEOREM LiftedCoreAliasCur ==
    \A aliasArg1 : LiftedSafety!Cur(aliasArg1) = Cur(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasMaxOr
   DEF Cur, LiftedSafety!Cur

THEOREM LiftedCoreAliasLastIndex ==
    \A aliasArg1 : LiftedSafety!LastIndex(aliasArg1) = LastIndex(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasMaxOr
   DEF LastIndex, LiftedSafety!LastIndex

THEOREM LiftedCoreAliasPart ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Part(aliasArg1, aliasArg2) = Part(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Part, LiftedSafety!Part

THEOREM LiftedCoreAliasPrefix ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Prefix(aliasArg1, aliasArg2) = Prefix(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Prefix, LiftedSafety!Prefix

THEOREM LiftedCoreAliasCount ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Count(aliasArg1, aliasArg2) = Count(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), LiftedCoreAliasCardinality, LiftedCoreAliasPart
   DEF Count, LiftedSafety!Count

THEOREM LiftedCoreAliasClosedPrefix ==
    \A aliasArg1 : LiftedSafety!ClosedPrefix(aliasArg1) = ClosedPrefix(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasCur, LiftedCoreAliasPrefix
   DEF ClosedPrefix, LiftedSafety!ClosedPrefix

THEOREM LiftedCoreAliasLastTerm ==
    \A aliasArg1 : LiftedSafety!LastTerm(aliasArg1) = LastTerm(aliasArg1)
BY ONLY ZenonT(10)
   DEF LastTerm, LiftedSafety!LastTerm, LastIndex, LiftedSafety!LastIndex,
       MaxOr, LiftedSafety!MaxOr
=============================================================================
