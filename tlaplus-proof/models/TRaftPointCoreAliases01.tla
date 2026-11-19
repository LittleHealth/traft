---------------------- MODULE TRaftPointCoreAliases01 ----------------------
EXTENDS TRaftPointLiftParameters

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasIsFiniteSet ==
    \A aliasArg1 : PointLift!IsFiniteSet(aliasArg1) = IsFiniteSet(aliasArg1)
BY ONLY ZenonT(10) DEF IsFiniteSet, PointLift!IsFiniteSet

THEOREM PointCoreAliasCardinality ==
    \A aliasArg1 : PointLift!Cardinality(aliasArg1) = Cardinality(aliasArg1)
BY ONLY ZenonT(10) DEF Cardinality, PointLift!Cardinality

THEOREM PointCoreAliasNoNode ==
    PointLift!NoNode = NoNode
BY ONLY ZenonT(10)
   DEF NoNode, PointLift!NoNode

THEOREM PointCoreAliasNoProposal ==
    PointLift!NoProposal = NoProposal
BY ONLY ZenonT(10)
   DEF NoProposal, PointLift!NoProposal

THEOREM PointCoreAliasNoReport ==
    PointLift!NoReport = NoReport
BY ONLY ZenonT(10)
   DEF NoReport, PointLift!NoReport

THEOREM PointCoreAliasRoles ==
    PointLift!Roles = Roles
BY ONLY ZenonT(10)
   DEF Roles, PointLift!Roles

THEOREM PointCoreAliasPhases ==
    PointLift!Phases = Phases
BY ONLY ZenonT(10)
   DEF Phases, PointLift!Phases

THEOREM PointCoreAliasTerms ==
    PointLift!Terms = Terms
BY ONLY ZenonT(10)
   DEF Terms, PointLift!Terms

THEOREM PointCoreAliasIndices ==
    PointLift!Indices = Indices
BY ONLY ZenonT(10)
   DEF Indices, PointLift!Indices

THEOREM PointCoreAliasPartitions ==
    PointLift!Partitions = Partitions
BY ONLY ZenonT(10)
   DEF Partitions, PointLift!Partitions
=============================================================================
