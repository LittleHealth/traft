---------------------- MODULE TRaftLiftedCoreAliases04 ----------------------
EXTENDS TRaftLiftedCoreAliases03

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasAck ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : LiftedSafety!Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Ack, LiftedSafety!Ack

THEOREM LiftedCoreAliasprotocolVars ==
    LiftedSafety!protocolVars = protocolVars
BY ONLY ZenonT(10)
   DEF protocolVars, LiftedSafety!protocolVars

THEOREM LiftedCoreAliasobserverVars ==
    LiftedSafety!observerVars = observerVars
BY ONLY ZenonT(10)
   DEF observerVars, LiftedSafety!observerVars

THEOREM LiftedCoreAliasvars ==
    LiftedSafety!vars = vars
BY ONLY ZenonT(10), LiftedCoreAliasprotocolVars, LiftedCoreAliasobserverVars
   DEF vars, LiftedSafety!vars

THEOREM LiftedCoreAliasEmptyReports ==
    LiftedSafety!EmptyReports = EmptyReports
BY ONLY ZenonT(10), LiftedCoreAliasNoReport
   DEF EmptyReports, LiftedSafety!EmptyReports

THEOREM LiftedCoreAliasReporters ==
    \A aliasArg1 : LiftedSafety!Reporters(aliasArg1) = Reporters(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasNoReport
   DEF Reporters, LiftedSafety!Reporters

THEOREM LiftedCoreAliasReportedProposals ==
    \A aliasArg1 : LiftedSafety!ReportedProposals(aliasArg1) = ReportedProposals(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasReporters
   DEF ReportedProposals, LiftedSafety!ReportedProposals

THEOREM LiftedCoreAliasReportedEntries ==
    \A aliasArg1 : LiftedSafety!ReportedEntries(aliasArg1) = ReportedEntries(aliasArg1)
BY ONLY ZenonT(10)
   DEF ReportedEntries, LiftedSafety!ReportedEntries, Result, LiftedSafety!Result,
       Reporters, LiftedSafety!Reporters, NoReport, LiftedSafety!NoReport

THEOREM LiftedCoreAliasRecovered ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Recovered(aliasArg1, aliasArg2) = Recovered(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Recovered, LiftedSafety!Recovered, NoProposal, LiftedSafety!NoProposal,
       Result, LiftedSafety!Result, ReportedEntries, LiftedSafety!ReportedEntries,
       Reporters, LiftedSafety!Reporters, NoReport, LiftedSafety!NoReport

THEOREM LiftedCoreAliasAligned ==
    \A aliasArg1, aliasArg2 : LiftedSafety!Aligned(aliasArg1, aliasArg2) = Aligned(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Aligned, LiftedSafety!Aligned
=============================================================================
