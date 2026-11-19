-------------------- MODULE TRaftUnboundedCoreAliases02 --------------------
EXTENDS TRaftUnboundedCoreAliases01

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasEntries ==
    UnboundedCore!Entries = Entries
BY ONLY ZenonT(10), UnboundedCoreAliasTerms, UnboundedCoreAliasIndices, UnboundedCoreAliasPartitions
   DEF Entries, UnboundedCore!Entries

THEOREM UnboundedCoreAliasProposalRecords ==
    UnboundedCore!ProposalRecords = ProposalRecords
BY ONLY ZenonT(10), UnboundedCoreAliasTerms, UnboundedCoreAliasEntries
   DEF ProposalRecords, UnboundedCore!ProposalRecords

THEOREM UnboundedCoreAliasMaxOr ==
    \A aliasArg1, aliasArg2 : UnboundedCore!MaxOr(aliasArg1, aliasArg2) = MaxOr(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF MaxOr, UnboundedCore!MaxOr

THEOREM UnboundedCoreAliasCur ==
    \A aliasArg1 : UnboundedCore!Cur(aliasArg1) = Cur(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasMaxOr
   DEF Cur, UnboundedCore!Cur

THEOREM UnboundedCoreAliasLastIndex ==
    \A aliasArg1 : UnboundedCore!LastIndex(aliasArg1) = LastIndex(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasMaxOr
   DEF LastIndex, UnboundedCore!LastIndex

THEOREM UnboundedCoreAliasPart ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Part(aliasArg1, aliasArg2) = Part(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Part, UnboundedCore!Part

THEOREM UnboundedCoreAliasPrefix ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Prefix(aliasArg1, aliasArg2) = Prefix(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Prefix, UnboundedCore!Prefix

THEOREM UnboundedCoreAliasCount ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Count(aliasArg1, aliasArg2) = Count(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedCoreAliasCardinality, UnboundedCoreAliasPart
   DEF Count, UnboundedCore!Count

THEOREM UnboundedCoreAliasClosedPrefix ==
    \A aliasArg1 : UnboundedCore!ClosedPrefix(aliasArg1) = ClosedPrefix(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasCur, UnboundedCoreAliasPrefix
   DEF ClosedPrefix, UnboundedCore!ClosedPrefix

THEOREM UnboundedCoreAliasLastTerm ==
    \A aliasArg1 : UnboundedCore!LastTerm(aliasArg1) = LastTerm(aliasArg1)
BY ONLY ZenonT(10)
   DEF LastTerm, UnboundedCore!LastTerm, LastIndex, UnboundedCore!LastIndex,
       MaxOr, UnboundedCore!MaxOr
=============================================================================
