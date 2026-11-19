----------------------- MODULE TRaftUnboundedSafetyProof --------------------
EXTENDS TRaftUnboundedCoreAliases11, TRaftProtocolSafety

THEOREM UnboundedSafetySpecificationIdentity == Spec <=> UnboundedCore!Spec
<1>1. (UnboundedCore!vars = vars)'
    BY ONLY PTL, UnboundedCoreAliasvars
<1>2. [UnboundedCore!Next]_UnboundedCore!vars <=> [Next]_vars
    BY ONLY SMT, UnboundedCoreAliasNext, UnboundedCoreAliasvars, <1>1
<1>3. UnboundedCore!Init <=> Init
    BY ONLY SMT, UnboundedCoreAliasInit
<1> QED BY ONLY PTL, <1>2, <1>3 DEF Spec, UnboundedCore!Spec

THEOREM UnboundedSafetyParameters ==
    UnboundedCore!ParameterAssumptions /\ UnboundedCore!SentinelSeparation
BY ONLY ParameterAssumptions, SentinelSeparation, UnboundedConstantSelections,
        UnboundedCoreAliasTerms, UnboundedCoreAliasIndices, UnboundedCoreAliasPartitions,
        UnboundedCoreAliasNoNode, UnboundedCoreAliasEntries, UnboundedCoreAliasProposalRecords,
        UnboundedCoreAliasIsFiniteSet, UnboundedCoreAliasCardinality
   DEF ParameterAssumptions, SentinelSeparation,
       UnboundedCore!ParameterAssumptions, UnboundedCore!SentinelSeparation

THEOREM UnboundedSafetyIdentity == Safety <=> UnboundedCore!Safety
BY ONLY UnboundedCoreAliasSafety

THEOREM UnboundedIdentifierDomains ==
    Terms = Nat /\ Indices = Nat \ {0} /\ Partitions = Nat
BY ONLY SMT, UnboundedConstantSelections DEF Terms, Indices, Partitions

THEOREM UnboundedProtocolSafety == UnboundedCore!Spec => []UnboundedCore!Safety
BY ONLY PTL, ProtocolSafety, UnboundedSafetySpecificationIdentity,
   UnboundedSafetyIdentity
=============================================================================
