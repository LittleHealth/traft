---------------------- MODULE TRaftPointCoreAliases08 ----------------------
EXTENDS TRaftPointCoreAliases07b

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasApplyEntry ==
    \A aliasArg1, aliasArg2 : PointLift!ApplyEntry(aliasArg1, aliasArg2) = ApplyEntry(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasPrefix
   DEF ApplyEntry, PointLift!ApplyEntry

THEOREM PointCoreAliasCrash ==
    \A aliasArg1 : PointLift!Crash(aliasArg1) = Crash(aliasArg1)
BY ONLY SMT, PointCoreAliasNoProposal, PointCoreAliasEmptyReports
   DEF Crash, PointLift!Crash

THEOREM PointCoreAliasRestart ==
    \A aliasArg1 : PointLift!Restart(aliasArg1) = Restart(aliasArg1)
BY ONLY SMT
   DEF Restart, PointLift!Restart

THEOREM PointCoreAliasAdministrativeNext ==
    PointLift!AdministrativeNext = AdministrativeNext
BY ONLY SMT, PointCoreAliasNoProposal, PointCoreAliasTerms, PointCoreAliasResult, PointCoreAliasLatest, PointCoreAliasReportedProposals, PointCoreAliasStartElection, PointCoreAliasAdoptTerm, PointCoreAliasGrantVote, PointCoreAliasDeliverVote, PointCoreAliasWinElection, PointCoreAliasMakeReport, PointCoreAliasDeliverReport, PointCoreAliasBuildRecovery, PointCoreAliasSendEntry, PointCoreAliasReceiveEntry, PointCoreAliasAckEntry, PointCoreAliasCopyProposalEntry, PointCoreAliasRetainProposal, PointCoreAliasAckProposal, PointCoreAliasDeliverAck, PointCoreAliasConfirmProposal, PointCoreAliasLearnConfirmation, PointCoreAliasCommitEntry, PointCoreAliasAdvertiseCommit, PointCoreAliasLearnCommit, PointCoreAliasActivate, PointCoreAliasCrash, PointCoreAliasRestart
   DEF AdministrativeNext, PointLift!AdministrativeNext

THEOREM PointCoreAliasProtocolNext ==
    PointLift!ProtocolNext = ProtocolNext
BY ONLY SMT, PointCoreAliasCreateEntry, PointCoreAliasCreateSuccessor, PointCoreAliasApplyEntry, PointCoreAliasAdministrativeNext
   DEF ProtocolNext, PointLift!ProtocolNext
=============================================================================
