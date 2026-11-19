---------------------- MODULE TRaftPointLiftInterface ----------------------
EXTENDS TRaftPointClientAliases02

THEOREM PointLiftInterfaceIdentities ==
    /\ (PointLift!ClientAction <=> ClientAction)
    /\ (PointLift!ElectionSafety <=> ElectionSafety)
    /\ (PointLift!RequestIdentityState <=> RequestIdentityState)
    /\ PointLift!Terms = Terms
    /\ (PointLift!ReadIsolation <=> ReadIsolation)
    /\ (PointLift!PartitionCommandsIndependent <=> PartitionCommandsIndependent)
    /\ \A C : PointLift!CanonicalPointLogs(C) <=> CanonicalPointLogs(C)
BY ONLY SMT, PointClientAliasClientAction, PointClientAliasElectionSafety, PointClientAliasRequestIdentityState, PointClientAliasReadIsolation, PointClientAliasPartitionCommandsIndependent, PointClientAliasCanonicalPointLogs, PointCoreAliasTerms
=============================================================================
