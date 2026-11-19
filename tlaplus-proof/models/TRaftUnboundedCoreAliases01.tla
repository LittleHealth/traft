-------------------- MODULE TRaftUnboundedCoreAliases01 --------------------
EXTENDS TRaftUnboundedSafetyDefinitions

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasIsFiniteSet ==
    \A aliasArg1 : UnboundedCore!IsFiniteSet(aliasArg1) = IsFiniteSet(aliasArg1)
BY ONLY ZenonT(10) DEF IsFiniteSet, UnboundedCore!IsFiniteSet

THEOREM UnboundedCoreAliasCardinality ==
    \A aliasArg1 : UnboundedCore!Cardinality(aliasArg1) = Cardinality(aliasArg1)
BY ONLY ZenonT(10) DEF Cardinality, UnboundedCore!Cardinality

THEOREM UnboundedCoreAliasNoNode ==
    UnboundedCore!NoNode = NoNode
BY ONLY ZenonT(10)
   DEF NoNode, UnboundedCore!NoNode

THEOREM UnboundedCoreAliasNoProposal ==
    UnboundedCore!NoProposal = NoProposal
BY ONLY ZenonT(10)
   DEF NoProposal, UnboundedCore!NoProposal

THEOREM UnboundedCoreAliasNoReport ==
    UnboundedCore!NoReport = NoReport
BY ONLY ZenonT(10)
   DEF NoReport, UnboundedCore!NoReport

THEOREM UnboundedCoreAliasRoles ==
    UnboundedCore!Roles = Roles
BY ONLY ZenonT(10)
   DEF Roles, UnboundedCore!Roles

THEOREM UnboundedCoreAliasPhases ==
    UnboundedCore!Phases = Phases
BY ONLY ZenonT(10)
   DEF Phases, UnboundedCore!Phases

THEOREM UnboundedCoreAliasTerms ==
    UnboundedCore!Terms = Terms
BY ONLY SMT, UnboundedConstantSelections
   DEF Terms, UnboundedCore!Terms

THEOREM UnboundedCoreAliasIndices ==
    UnboundedCore!Indices = Indices
BY ONLY SMT, UnboundedConstantSelections
   DEF Indices, UnboundedCore!Indices

THEOREM UnboundedCoreAliasPartitions ==
    UnboundedCore!Partitions = Partitions
BY ONLY SMT, UnboundedConstantSelections
   DEF Partitions, UnboundedCore!Partitions
=============================================================================
