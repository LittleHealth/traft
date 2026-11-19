---------------------- MODULE TRaftPointLiftParameters ----------------------
EXTENDS TRaftPointLiftDefinitions

\* Proof-only instance sharing and transport; no protocol guard or premise.

THEOREM PointLiftParameters ==
    /\ PointLift!ParameterAssumptions /\ PointLift!SentinelSeparation
    /\ PointLift!ClientParameters /\ PointLift!FormalFaultsDisabled
BY ONLY ParameterAssumptions, SentinelSeparation, ClientParameters, FormalFaultsDisabled
   DEF PointLift!FormalFaultsDisabled, FormalFaultsDisabled, PointLift!ParameterAssumptions, ParameterAssumptions, PointLift!SentinelSeparation,
       SentinelSeparation, PointLift!ClientParameters, ClientParameters, PointLift!NoNode, NoNode,
       PointLift!Terms, Terms, PointLift!Indices, Indices, PointLift!Partitions, Partitions,
       PointLift!Entries, Entries, PointLift!ProposalRecords, ProposalRecords,
       PointLift!ClientCommands, ClientCommands, PointLift!RequestIds, RequestIds,
       PointLift!SeqDomain, SeqDomain, PointLift!Keys, Keys, PointLift!IsFiniteSet, IsFiniteSet,
       PointLift!Cardinality, Cardinality
=============================================================================
