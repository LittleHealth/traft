-------------------- MODULE TRaftUnboundedCoreAliases04 --------------------
EXTENDS TRaftUnboundedCoreAliases03

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasAck ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : UnboundedCore!Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Ack, UnboundedCore!Ack

THEOREM UnboundedCoreAliasprotocolVars ==
    UnboundedCore!protocolVars = protocolVars
BY ONLY ZenonT(10)
   DEF protocolVars, UnboundedCore!protocolVars

THEOREM UnboundedCoreAliasobserverVars ==
    UnboundedCore!observerVars = observerVars
BY ONLY ZenonT(10)
   DEF observerVars, UnboundedCore!observerVars

THEOREM UnboundedCoreAliasvars ==
    UnboundedCore!vars = vars
BY ONLY ZenonT(10), UnboundedCoreAliasprotocolVars, UnboundedCoreAliasobserverVars
   DEF vars, UnboundedCore!vars

THEOREM UnboundedCoreAliasEmptyReports ==
    UnboundedCore!EmptyReports = EmptyReports
BY ONLY ZenonT(10), UnboundedCoreAliasNoReport
   DEF EmptyReports, UnboundedCore!EmptyReports

THEOREM UnboundedCoreAliasReporters ==
    \A aliasArg1 : UnboundedCore!Reporters(aliasArg1) = Reporters(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasNoReport
   DEF Reporters, UnboundedCore!Reporters

THEOREM UnboundedCoreAliasReportedProposals ==
    \A aliasArg1 : UnboundedCore!ReportedProposals(aliasArg1) = ReportedProposals(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasReporters
   DEF ReportedProposals, UnboundedCore!ReportedProposals

THEOREM UnboundedCoreAliasReportedEntries ==
    \A aliasArg1 : UnboundedCore!ReportedEntries(aliasArg1) = ReportedEntries(aliasArg1)
BY ONLY ZenonT(10)
   DEF ReportedEntries, UnboundedCore!ReportedEntries, Result, UnboundedCore!Result,
       Reporters, UnboundedCore!Reporters, NoReport, UnboundedCore!NoReport

THEOREM UnboundedCoreAliasRecovered ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Recovered(aliasArg1, aliasArg2) = Recovered(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedConstantSelections
   DEF Recovered, UnboundedCore!Recovered, NoProposal, UnboundedCore!NoProposal,
       Result, UnboundedCore!Result, ReportedEntries, UnboundedCore!ReportedEntries,
       Reporters, UnboundedCore!Reporters, NoReport, UnboundedCore!NoReport

THEOREM UnboundedCoreAliasAligned ==
    \A aliasArg1, aliasArg2 : UnboundedCore!Aligned(aliasArg1, aliasArg2) = Aligned(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Aligned, UnboundedCore!Aligned
=============================================================================
