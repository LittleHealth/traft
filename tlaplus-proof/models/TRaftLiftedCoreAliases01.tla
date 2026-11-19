---------------------- MODULE TRaftLiftedCoreAliases01 ----------------------
EXTENDS TRaftLiftedProtocolDefinitions

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasIsFiniteSet ==
    \A aliasArg1 : LiftedSafety!IsFiniteSet(aliasArg1) = IsFiniteSet(aliasArg1)
BY ONLY ZenonT(10) DEF IsFiniteSet, LiftedSafety!IsFiniteSet

THEOREM LiftedCoreAliasCardinality ==
    \A aliasArg1 : LiftedSafety!Cardinality(aliasArg1) = Cardinality(aliasArg1)
BY ONLY ZenonT(10) DEF Cardinality, LiftedSafety!Cardinality

THEOREM LiftedCoreAliasNoNode ==
    LiftedSafety!NoNode = NoNode
BY ONLY ZenonT(10)
   DEF NoNode, LiftedSafety!NoNode

THEOREM LiftedCoreAliasNoProposal ==
    LiftedSafety!NoProposal = NoProposal
BY ONLY ZenonT(10)
   DEF NoProposal, LiftedSafety!NoProposal

THEOREM LiftedCoreAliasNoReport ==
    LiftedSafety!NoReport = NoReport
BY ONLY ZenonT(10)
   DEF NoReport, LiftedSafety!NoReport

THEOREM LiftedCoreAliasRoles ==
    LiftedSafety!Roles = Roles
BY ONLY ZenonT(10)
   DEF Roles, LiftedSafety!Roles

THEOREM LiftedCoreAliasPhases ==
    LiftedSafety!Phases = Phases
BY ONLY ZenonT(10)
   DEF Phases, LiftedSafety!Phases

THEOREM LiftedCoreAliasTerms ==
    LiftedSafety!Terms = Terms
BY ONLY ZenonT(10)
   DEF Terms, LiftedSafety!Terms

THEOREM LiftedCoreAliasIndices ==
    LiftedSafety!Indices = Indices
BY ONLY ZenonT(10)
   DEF Indices, LiftedSafety!Indices

THEOREM LiftedCoreAliasPartitions ==
    LiftedSafety!Partitions = Partitions
BY ONLY ZenonT(10)
   DEF Partitions, LiftedSafety!Partitions
=============================================================================
