-------------------- MODULE TRaftUnboundedClientCoreAliases04 --------------------
EXTENDS TRaftUnboundedClientCoreAliases03

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasAck ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5 : UnboundedClient!Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5) = Ack(aliasArg1, aliasArg2, aliasArg3, aliasArg4, aliasArg5)
BY ONLY ZenonT(10)
   DEF Ack, UnboundedClient!Ack

THEOREM UnboundedClientCoreAliasprotocolVars ==
    UnboundedClient!protocolVars = protocolVars
BY ONLY ZenonT(10)
   DEF protocolVars, UnboundedClient!protocolVars

THEOREM UnboundedClientCoreAliasobserverVars ==
    UnboundedClient!observerVars = observerVars
BY ONLY ZenonT(10)
   DEF observerVars, UnboundedClient!observerVars

THEOREM UnboundedClientCoreAliasvars ==
    UnboundedClient!vars = vars
BY ONLY ZenonT(10), UnboundedClientCoreAliasprotocolVars, UnboundedClientCoreAliasobserverVars
   DEF vars, UnboundedClient!vars

THEOREM UnboundedClientCoreAliasEmptyReports ==
    UnboundedClient!EmptyReports = EmptyReports
BY ONLY ZenonT(10), UnboundedClientCoreAliasNoReport
   DEF EmptyReports, UnboundedClient!EmptyReports

THEOREM UnboundedClientCoreAliasReporters ==
    \A aliasArg1 : UnboundedClient!Reporters(aliasArg1) = Reporters(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasNoReport
   DEF Reporters, UnboundedClient!Reporters

THEOREM UnboundedClientCoreAliasReportedProposals ==
    \A aliasArg1 : UnboundedClient!ReportedProposals(aliasArg1) = ReportedProposals(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasReporters
   DEF ReportedProposals, UnboundedClient!ReportedProposals

THEOREM UnboundedClientCoreAliasReportedEntries ==
    \A aliasArg1 : UnboundedClient!ReportedEntries(aliasArg1) = ReportedEntries(aliasArg1)
BY ONLY ZenonT(10)
   DEF ReportedEntries, UnboundedClient!ReportedEntries, Result, UnboundedClient!Result,
       Reporters, UnboundedClient!Reporters, NoReport, UnboundedClient!NoReport

THEOREM UnboundedClientCoreAliasRecovered ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Recovered(aliasArg1, aliasArg2) = Recovered(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientConstantSelections
   DEF Recovered, UnboundedClient!Recovered, NoProposal, UnboundedClient!NoProposal,
       Result, UnboundedClient!Result, ReportedEntries, UnboundedClient!ReportedEntries,
       Reporters, UnboundedClient!Reporters, NoReport, UnboundedClient!NoReport

THEOREM UnboundedClientCoreAliasAligned ==
    \A aliasArg1, aliasArg2 : UnboundedClient!Aligned(aliasArg1, aliasArg2) = Aligned(aliasArg1, aliasArg2)
BY ONLY ZenonT(10)
   DEF Aligned, UnboundedClient!Aligned
=============================================================================
