---------------------- MODULE TRaftPointCoreAliases04 ----------------------
EXTENDS TRaftPointCoreAliases03

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasAck ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : PointLift!Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Ack, PointLift!Ack

THEOREM PointCoreAliasprotocolVars ==
    PointLift!protocolVars = protocolVars
BY ONLY ZenonT(10)
   DEF protocolVars, PointLift!protocolVars

THEOREM PointCoreAliasobserverVars ==
    PointLift!observerVars = observerVars
BY ONLY ZenonT(10)
   DEF observerVars, PointLift!observerVars

THEOREM PointCoreAliasvars ==
    PointLift!vars = vars
BY ONLY ZenonT(10), PointCoreAliasprotocolVars, PointCoreAliasobserverVars
   DEF vars, PointLift!vars

THEOREM PointCoreAliasEmptyReports ==
    PointLift!EmptyReports = EmptyReports
BY ONLY ZenonT(10), PointCoreAliasNoReport
   DEF EmptyReports, PointLift!EmptyReports

THEOREM PointCoreAliasReporters ==
    \A aliasArg1 : PointLift!Reporters(aliasArg1) = Reporters(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasNoReport
   DEF Reporters, PointLift!Reporters

THEOREM PointCoreAliasReportedProposals ==
    \A aliasArg1 : PointLift!ReportedProposals(aliasArg1) = ReportedProposals(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasReporters
   DEF ReportedProposals, PointLift!ReportedProposals

THEOREM PointCoreAliasReportedEntries ==
    \A aliasArg1 : PointLift!ReportedEntries(aliasArg1) = ReportedEntries(aliasArg1)
BY ONLY ZenonT(10)
   DEF ReportedEntries, PointLift!ReportedEntries, Result, PointLift!Result,
       Reporters, PointLift!Reporters, NoReport, PointLift!NoReport

THEOREM PointCoreAliasRecovered ==
    \A aliasArg1, aliasArg2 : PointLift!Recovered(aliasArg1, aliasArg2) = Recovered(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Recovered, PointLift!Recovered, NoProposal, PointLift!NoProposal,
       Result, PointLift!Result, ReportedEntries, PointLift!ReportedEntries,
       Reporters, PointLift!Reporters, NoReport, PointLift!NoReport

THEOREM PointCoreAliasAligned ==
    \A aliasArg1, aliasArg2 : PointLift!Aligned(aliasArg1, aliasArg2) = Aligned(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Aligned, PointLift!Aligned
=============================================================================
