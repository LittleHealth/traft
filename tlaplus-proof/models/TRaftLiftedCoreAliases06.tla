---------------------- MODULE TRaftLiftedCoreAliases06 ----------------------
EXTENDS TRaftLiftedCoreAliases05

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasDeliverVote ==
    \A aliasArg1, aliasArg2 : LiftedSafety!DeliverVote(aliasArg1, aliasArg2) = DeliverVote(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverVote, LiftedSafety!DeliverVote

THEOREM LiftedCoreAliasWinElection ==
    \A aliasArg1 : LiftedSafety!WinElection(aliasArg1) = WinElection(aliasArg1)
BY ONLY SMT, LiftedCoreAliasQuorum
   DEF WinElection, LiftedSafety!WinElection

THEOREM LiftedCoreAliasMakeReport ==
    \A aliasArg1, aliasArg2 : LiftedSafety!MakeReport(aliasArg1, aliasArg2) = MakeReport(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF MakeReport, LiftedSafety!MakeReport

THEOREM LiftedCoreAliasDeliverReport ==
    \A aliasArg1, aliasArg2 : LiftedSafety!DeliverReport(aliasArg1, aliasArg2) = DeliverReport(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasNoReport
   DEF DeliverReport, LiftedSafety!DeliverReport

THEOREM LiftedCoreAliasBuildRecovery ==
    \A aliasArg1, aliasArg2 : LiftedSafety!BuildRecovery(aliasArg1, aliasArg2) = BuildRecovery(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasNoProposal, LiftedCoreAliasIndices, LiftedCoreAliasPartitions, LiftedCoreAliasCur, LiftedCoreAliasLastIndex, LiftedCoreAliasCount, LiftedCoreAliasQuorum, LiftedCoreAliasEntry, LiftedCoreAliasProposal, LiftedCoreAliasLatest, LiftedCoreAliasReporters, LiftedCoreAliasReportedProposals, LiftedCoreAliasReportedEntries, LiftedCoreAliasRecovered
   DEF BuildRecovery, LiftedSafety!BuildRecovery

THEOREM LiftedCoreAliasCreateEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!CreateEntry(aliasArg1, aliasArg2) = CreateEntry(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasIndices, LiftedCoreAliasCur, LiftedCoreAliasLastIndex, LiftedCoreAliasCount, LiftedCoreAliasOrigin, LiftedCoreAliasEntry, LiftedCoreAliasAligned
   DEF CreateEntry, LiftedSafety!CreateEntry

THEOREM LiftedCoreAliasCreateSuccessor ==
    \A aliasArg1, aliasArg2, aliasArg3 : LiftedSafety!CreateSuccessor(aliasArg1, aliasArg2, aliasArg3) = CreateSuccessor(aliasArg1, aliasArg2, aliasArg3)
BY ONLY SMT, LiftedCoreAliasIndices, LiftedCoreAliasPartitions, LiftedCoreAliasCur, LiftedCoreAliasLastIndex, LiftedCoreAliasPart, LiftedCoreAliasCount, LiftedCoreAliasEntry, LiftedCoreAliasAligned
   DEF CreateSuccessor, LiftedSafety!CreateSuccessor

THEOREM LiftedCoreAliasSendEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!SendEntry(aliasArg1, aliasArg2) = SendEntry(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasNormalMessage
   DEF SendEntry, LiftedSafety!SendEntry

THEOREM LiftedCoreAliasReceiveEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!ReceiveEntry(aliasArg1, aliasArg2) = ReceiveEntry(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasCanReceive
   DEF ReceiveEntry, LiftedSafety!ReceiveEntry

THEOREM LiftedCoreAliasAckEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!AckEntry(aliasArg1, aliasArg2) = AckEntry(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasAck
   DEF AckEntry, LiftedSafety!AckEntry
=============================================================================
