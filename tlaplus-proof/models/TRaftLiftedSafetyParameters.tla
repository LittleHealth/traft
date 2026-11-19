---------------------- MODULE TRaftLiftedSafetyParameters ----------------------
EXTENDS TRaftLiftedCoreAliases11

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedSafetyParameters ==
    /\ LiftedSafety!ParameterAssumptions /\ LiftedSafety!SentinelSeparation
    /\ LiftedSafety!FormalFaultsDisabled /\ LiftedSafety!CommitProofFaultsDisabled
BY ONLY ZenonT(10), ParameterAssumptions, SentinelSeparation, FormalFaultsDisabled
   DEF ParameterAssumptions, LiftedSafety!ParameterAssumptions,
       SentinelSeparation, LiftedSafety!SentinelSeparation,
       FormalFaultsDisabled, LiftedSafety!FormalFaultsDisabled,
       LiftedSafety!CommitProofFaultsDisabled, LiftedSafety!CommitFaultsDisabled,
       NoNode, LiftedSafety!NoNode, Terms, LiftedSafety!Terms,
       Indices, LiftedSafety!Indices, Partitions, LiftedSafety!Partitions,
       Entries, LiftedSafety!Entries, ProposalRecords, LiftedSafety!ProposalRecords,
       IsFiniteSet, LiftedSafety!IsFiniteSet, Cardinality, LiftedSafety!Cardinality

THEOREM LiftedSafetyPredicateIdentity == LiftedSafety!Safety <=> Safety
BY ONLY LiftedCoreAliasSafety
=============================================================================
