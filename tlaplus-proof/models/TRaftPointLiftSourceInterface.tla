---------------------- MODULE TRaftPointLiftSourceInterface ----------------------
EXTENDS TRaftPointLiftInterface

\* Proof-only instance sharing and transport; no protocol guard or premise.

THEOREM SourceLiftInterfaceIdentities ==
    /\ (PointLift!ClientAction <=> ClientAction)
    /\ (PointLift!ElectionSafety <=> ElectionSafety)
    /\ PointLift!Terms = Terms
    /\ PointLift!ClientCommands = ClientCommands
    /\ \A C, Q : PointLift!CanonicalDataFrom(C, Q) <=> CanonicalDataFrom(C, Q)
    /\ \A F, Q : PointLift!FormalDataFrom(F, Q) <=> FormalDataFrom(F, Q)
BY ONLY IsaM("auto"), PointLiftInterfaceIdentities
   DEF PointLift!ClientCommands, ClientCommands, PointLift!RequestIds, RequestIds,
       PointLift!SeqDomain, SeqDomain, PointLift!Keys, Keys,
       PointLift!CanonicalDataFrom, CanonicalDataFrom,
       PointLift!FormalDataFrom, FormalDataFrom, PointLift!LogDataFrom, LogDataFrom
=============================================================================
