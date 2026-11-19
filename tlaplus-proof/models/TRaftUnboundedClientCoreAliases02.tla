-------------------- MODULE TRaftUnboundedClientCoreAliases02 --------------------
EXTENDS TRaftUnboundedClientCoreAliases01

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasEntries ==
    UnboundedClient!Entries = Entries
BY ONLY ZenonT(10), UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasIndices, UnboundedClientCoreAliasPartitions, UnboundedClientDomains
   DEF Entries, UnboundedClient!Entries

THEOREM UnboundedClientCoreAliasProposalRecords ==
    UnboundedClient!ProposalRecords = ProposalRecords
BY ONLY ZenonT(10), UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasEntries
   DEF ProposalRecords, UnboundedClient!ProposalRecords

THEOREM UnboundedClientCoreAliasMaxOr ==
    \A aliasArg1, aliasArg2 : UnboundedClient!MaxOr(aliasArg1, aliasArg2) = MaxOr(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF MaxOr, UnboundedClient!MaxOr

THEOREM UnboundedClientCoreAliasCur ==
    \A aliasArg1 : UnboundedClient!Cur(aliasArg1) = Cur(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasMaxOr
   DEF Cur, UnboundedClient!Cur

THEOREM UnboundedClientCoreAliasLastIndex ==
    \A aliasArg1 : UnboundedClient!LastIndex(aliasArg1) = LastIndex(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasMaxOr
   DEF LastIndex, UnboundedClient!LastIndex

THEOREM UnboundedClientCoreAliasPart ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Part(aliasArg1, aliasArg2) = Part(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Part, UnboundedClient!Part

THEOREM UnboundedClientCoreAliasPrefix ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Prefix(aliasArg1, aliasArg2) = Prefix(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Prefix, UnboundedClient!Prefix

THEOREM UnboundedClientCoreAliasCount ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Count(aliasArg1, aliasArg2) = Count(aliasArg1, aliasArg2)
BY ONLY ZenonT(10), UnboundedClientCoreAliasCardinality, UnboundedClientCoreAliasPart
   DEF Count, UnboundedClient!Count

THEOREM UnboundedClientCoreAliasClosedPrefix ==
    \A aliasArg1 : UnboundedClient!ClosedPrefix(aliasArg1) = ClosedPrefix(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasCur, UnboundedClientCoreAliasPrefix
   DEF ClosedPrefix, UnboundedClient!ClosedPrefix

THEOREM UnboundedClientCoreAliasLastTerm ==
    \A aliasArg1 : UnboundedClient!LastTerm(aliasArg1) = LastTerm(aliasArg1)
BY ONLY ZenonT(10)
   DEF LastTerm, UnboundedClient!LastTerm, LastIndex, UnboundedClient!LastIndex,
       MaxOr, UnboundedClient!MaxOr
=============================================================================
