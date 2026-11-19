---------------------- MODULE TRaftPointCoreAliases06 ----------------------
EXTENDS TRaftPointCoreAliases05

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasDeliverVote ==
    \A aliasArg1, aliasArg2 : PointLift!DeliverVote(aliasArg1, aliasArg2) = DeliverVote(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverVote, PointLift!DeliverVote

THEOREM PointCoreAliasWinElection ==
    \A aliasArg1 : PointLift!WinElection(aliasArg1) = WinElection(aliasArg1)
BY ONLY SMT, PointCoreAliasQuorum
   DEF WinElection, PointLift!WinElection

THEOREM PointCoreAliasMakeReport ==
    \A aliasArg1, aliasArg2 : PointLift!MakeReport(aliasArg1, aliasArg2) = MakeReport(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF MakeReport, PointLift!MakeReport

THEOREM PointCoreAliasDeliverReport ==
    \A aliasArg1, aliasArg2 : PointLift!DeliverReport(aliasArg1, aliasArg2) = DeliverReport(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasNoReport
   DEF DeliverReport, PointLift!DeliverReport

THEOREM PointCoreAliasBuildRecovery ==
    \A aliasArg1, aliasArg2 : PointLift!BuildRecovery(aliasArg1, aliasArg2) = BuildRecovery(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasNoProposal, PointCoreAliasIndices, PointCoreAliasPartitions, PointCoreAliasCur, PointCoreAliasLastIndex, PointCoreAliasCount, PointCoreAliasQuorum, PointCoreAliasEntry, PointCoreAliasProposal, PointCoreAliasLatest, PointCoreAliasReporters, PointCoreAliasReportedProposals, PointCoreAliasReportedEntries, PointCoreAliasRecovered
   DEF BuildRecovery, PointLift!BuildRecovery

THEOREM PointCoreAliasCreateEntry ==
    \A aliasArg1, aliasArg2 : PointLift!CreateEntry(aliasArg1, aliasArg2) = CreateEntry(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasIndices, PointCoreAliasCur, PointCoreAliasLastIndex, PointCoreAliasCount, PointCoreAliasOrigin, PointCoreAliasEntry, PointCoreAliasAligned
   DEF CreateEntry, PointLift!CreateEntry

THEOREM PointCoreAliasCreateSuccessor ==
    \A aliasArg1, aliasArg2, aliasArg3 : PointLift!CreateSuccessor(aliasArg1, aliasArg2, aliasArg3) = CreateSuccessor(aliasArg1, aliasArg2, aliasArg3)
BY ONLY SMT, PointCoreAliasIndices, PointCoreAliasPartitions, PointCoreAliasCur, PointCoreAliasLastIndex, PointCoreAliasPart, PointCoreAliasCount, PointCoreAliasEntry, PointCoreAliasAligned
   DEF CreateSuccessor, PointLift!CreateSuccessor

THEOREM PointCoreAliasSendEntry ==
    \A aliasArg1, aliasArg2 : PointLift!SendEntry(aliasArg1, aliasArg2) = SendEntry(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasNormalMessage
   DEF SendEntry, PointLift!SendEntry

THEOREM PointCoreAliasReceiveEntry ==
    \A aliasArg1, aliasArg2 : PointLift!ReceiveEntry(aliasArg1, aliasArg2) = ReceiveEntry(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasCanReceive
   DEF ReceiveEntry, PointLift!ReceiveEntry

THEOREM PointCoreAliasAckEntry ==
    \A aliasArg1, aliasArg2 : PointLift!AckEntry(aliasArg1, aliasArg2) = AckEntry(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasAck
   DEF AckEntry, PointLift!AckEntry
=============================================================================
