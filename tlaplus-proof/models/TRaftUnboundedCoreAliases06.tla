-------------------- MODULE TRaftUnboundedCoreAliases06 --------------------
EXTENDS TRaftUnboundedCoreAliases05

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasDeliverVote ==
    \A aliasArg1, aliasArg2 : UnboundedCore!DeliverVote(aliasArg1, aliasArg2) = DeliverVote(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverVote, UnboundedCore!DeliverVote

THEOREM UnboundedCoreAliasWinElection ==
    \A aliasArg1 : UnboundedCore!WinElection(aliasArg1) = WinElection(aliasArg1)
BY ONLY SMT, UnboundedCoreAliasQuorum
   DEF WinElection, UnboundedCore!WinElection

THEOREM UnboundedCoreAliasMakeReport ==
    \A aliasArg1, aliasArg2 : UnboundedCore!MakeReport(aliasArg1, aliasArg2) = MakeReport(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedConstantSelections
   DEF MakeReport, UnboundedCore!MakeReport

THEOREM UnboundedCoreAliasDeliverReport ==
    \A aliasArg1, aliasArg2 : UnboundedCore!DeliverReport(aliasArg1, aliasArg2) = DeliverReport(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasNoReport
   DEF DeliverReport, UnboundedCore!DeliverReport

THEOREM UnboundedCoreAliasBuildRecovery ==
    \A aliasArg1, aliasArg2 : UnboundedCore!BuildRecovery(aliasArg1, aliasArg2) = BuildRecovery(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasNoProposal, UnboundedCoreAliasIndices, UnboundedCoreAliasPartitions, UnboundedCoreAliasCur, UnboundedCoreAliasLastIndex, UnboundedCoreAliasCount, UnboundedCoreAliasQuorum, UnboundedCoreAliasEntry, UnboundedCoreAliasProposal, UnboundedCoreAliasLatest, UnboundedCoreAliasReporters, UnboundedCoreAliasReportedProposals, UnboundedCoreAliasReportedEntries, UnboundedCoreAliasRecovered
   DEF BuildRecovery, UnboundedCore!BuildRecovery

THEOREM UnboundedCoreAliasCreateEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!CreateEntry(aliasArg1, aliasArg2) = CreateEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasIndices, UnboundedCoreAliasCur, UnboundedCoreAliasLastIndex, UnboundedCoreAliasCount, UnboundedCoreAliasOrigin, UnboundedCoreAliasEntry, UnboundedCoreAliasAligned
   DEF CreateEntry, UnboundedCore!CreateEntry

THEOREM UnboundedCoreAliasCreateSuccessor ==
    \A aliasArg1, aliasArg2, aliasArg3 : UnboundedCore!CreateSuccessor(aliasArg1, aliasArg2, aliasArg3) = CreateSuccessor(aliasArg1, aliasArg2, aliasArg3)
BY ONLY SMT, UnboundedCoreAliasIndices, UnboundedCoreAliasPartitions, UnboundedCoreAliasCur, UnboundedCoreAliasLastIndex, UnboundedCoreAliasPart, UnboundedCoreAliasCount, UnboundedCoreAliasEntry, UnboundedCoreAliasAligned
   DEF CreateSuccessor, UnboundedCore!CreateSuccessor

THEOREM UnboundedCoreAliasSendEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!SendEntry(aliasArg1, aliasArg2) = SendEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasNormalMessage
   DEF SendEntry, UnboundedCore!SendEntry

THEOREM UnboundedCoreAliasReceiveEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!ReceiveEntry(aliasArg1, aliasArg2) = ReceiveEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasCanReceive
   DEF ReceiveEntry, UnboundedCore!ReceiveEntry

THEOREM UnboundedCoreAliasAckEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!AckEntry(aliasArg1, aliasArg2) = AckEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasAck
   DEF AckEntry, UnboundedCore!AckEntry
=============================================================================
