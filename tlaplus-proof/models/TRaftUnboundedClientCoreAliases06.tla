-------------------- MODULE TRaftUnboundedClientCoreAliases06 --------------------
EXTENDS TRaftUnboundedClientCoreAliases05

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasDeliverVote ==
    \A aliasArg1, aliasArg2 : UnboundedClient!DeliverVote(aliasArg1, aliasArg2) = DeliverVote(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverVote, UnboundedClient!DeliverVote

THEOREM UnboundedClientCoreAliasWinElection ==
    \A aliasArg1 : UnboundedClient!WinElection(aliasArg1) = WinElection(aliasArg1)
BY ONLY SMT, UnboundedClientCoreAliasQuorum
   DEF WinElection, UnboundedClient!WinElection

THEOREM UnboundedClientCoreAliasMakeReport ==
    \A aliasArg1, aliasArg2 : UnboundedClient!MakeReport(aliasArg1, aliasArg2) = MakeReport(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientConstantSelections
   DEF MakeReport, UnboundedClient!MakeReport

THEOREM UnboundedClientCoreAliasDeliverReport ==
    \A aliasArg1, aliasArg2 : UnboundedClient!DeliverReport(aliasArg1, aliasArg2) = DeliverReport(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasNoReport
   DEF DeliverReport, UnboundedClient!DeliverReport

THEOREM UnboundedClientCoreAliasBuildRecovery ==
    \A aliasArg1, aliasArg2 : UnboundedClient!BuildRecovery(aliasArg1, aliasArg2) = BuildRecovery(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasIndices, UnboundedClientCoreAliasPartitions, UnboundedClientCoreAliasCur, UnboundedClientCoreAliasLastIndex, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasEntry, UnboundedClientCoreAliasProposal, UnboundedClientCoreAliasLatest, UnboundedClientCoreAliasReporters, UnboundedClientCoreAliasReportedProposals, UnboundedClientCoreAliasReportedEntries, UnboundedClientCoreAliasRecovered
   DEF BuildRecovery, UnboundedClient!BuildRecovery

THEOREM UnboundedClientCoreAliasCreateEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!CreateEntry(aliasArg1, aliasArg2) = CreateEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasIndices, UnboundedClientCoreAliasCur, UnboundedClientCoreAliasLastIndex, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasOrigin, UnboundedClientCoreAliasEntry, UnboundedClientCoreAliasAligned, UnboundedClientDomains
   DEF CreateEntry, UnboundedClient!CreateEntry

THEOREM UnboundedClientCoreAliasCreateSuccessor ==
    \A aliasArg1, aliasArg2, aliasArg3 : UnboundedClient!CreateSuccessor(aliasArg1, aliasArg2, aliasArg3) = CreateSuccessor(aliasArg1, aliasArg2, aliasArg3)
BY ONLY SMT, UnboundedClientCoreAliasIndices, UnboundedClientCoreAliasPartitions, UnboundedClientCoreAliasCur, UnboundedClientCoreAliasLastIndex, UnboundedClientCoreAliasPart, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasEntry, UnboundedClientCoreAliasAligned, UnboundedClientDomains
   DEF CreateSuccessor, UnboundedClient!CreateSuccessor

THEOREM UnboundedClientCoreAliasSendEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!SendEntry(aliasArg1, aliasArg2) = SendEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasNormalMessage
   DEF SendEntry, UnboundedClient!SendEntry

THEOREM UnboundedClientCoreAliasReceiveEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!ReceiveEntry(aliasArg1, aliasArg2) = ReceiveEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasCanReceive
   DEF ReceiveEntry, UnboundedClient!ReceiveEntry

THEOREM UnboundedClientCoreAliasAckEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!AckEntry(aliasArg1, aliasArg2) = AckEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasAck
   DEF AckEntry, UnboundedClient!AckEntry
=============================================================================
