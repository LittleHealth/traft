-------------------- MODULE TRaftUnboundedClientCoreAliases01 --------------------
EXTENDS TRaftUnboundedClientDefinitions

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasIsFiniteSet ==
    \A aliasArg1 : UnboundedClient!IsFiniteSet(aliasArg1) = IsFiniteSet(aliasArg1)
BY ONLY ZenonT(10) DEF IsFiniteSet, UnboundedClient!IsFiniteSet

THEOREM UnboundedClientCoreAliasCardinality ==
    \A aliasArg1 : UnboundedClient!Cardinality(aliasArg1) = Cardinality(aliasArg1)
BY ONLY ZenonT(10) DEF Cardinality, UnboundedClient!Cardinality

THEOREM UnboundedClientCoreAliasNoNode ==
    UnboundedClient!NoNode = NoNode
BY ONLY ZenonT(10)
   DEF NoNode, UnboundedClient!NoNode

THEOREM UnboundedClientCoreAliasNoProposal ==
    UnboundedClient!NoProposal = NoProposal
BY ONLY ZenonT(10)
   DEF NoProposal, UnboundedClient!NoProposal

THEOREM UnboundedClientCoreAliasNoReport ==
    UnboundedClient!NoReport = NoReport
BY ONLY ZenonT(10)
   DEF NoReport, UnboundedClient!NoReport

THEOREM UnboundedClientCoreAliasRoles ==
    UnboundedClient!Roles = Roles
BY ONLY ZenonT(10)
   DEF Roles, UnboundedClient!Roles

THEOREM UnboundedClientCoreAliasPhases ==
    UnboundedClient!Phases = Phases
BY ONLY ZenonT(10)
   DEF Phases, UnboundedClient!Phases

THEOREM UnboundedClientCoreAliasTerms ==
    UnboundedClient!Terms = Terms
BY ONLY SMT, UnboundedClientConstantSelections
   DEF Terms, UnboundedClient!Terms

THEOREM UnboundedClientCoreAliasIndices ==
    UnboundedClient!Indices = Indices
BY ONLY SMT, UnboundedClientConstantSelections
   DEF Indices, UnboundedClient!Indices

THEOREM UnboundedClientCoreAliasPartitions ==
    UnboundedClient!Partitions = Partitions
BY ONLY SMT, UnboundedClientConstantSelections
   DEF Partitions, UnboundedClient!Partitions
=============================================================================
