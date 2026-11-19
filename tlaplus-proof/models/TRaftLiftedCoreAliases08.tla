---------------------- MODULE TRaftLiftedCoreAliases08 ----------------------
EXTENDS TRaftLiftedCoreAliases07b

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasApplyEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!ApplyEntry(aliasArg1, aliasArg2) = ApplyEntry(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasPrefix
   DEF ApplyEntry, LiftedSafety!ApplyEntry

THEOREM LiftedCoreAliasCrash ==
    \A aliasArg1 : LiftedSafety!Crash(aliasArg1) = Crash(aliasArg1)
BY ONLY SMT, LiftedCoreAliasNoProposal, LiftedCoreAliasEmptyReports
   DEF Crash, LiftedSafety!Crash

THEOREM LiftedCoreAliasRestart ==
    \A aliasArg1 : LiftedSafety!Restart(aliasArg1) = Restart(aliasArg1)
BY ONLY SMT
   DEF Restart, LiftedSafety!Restart

THEOREM LiftedCoreAliasAdministrativeNext ==
    LiftedSafety!AdministrativeNext = AdministrativeNext
BY ONLY SMT, LiftedCoreAliasNoProposal, LiftedCoreAliasTerms, LiftedCoreAliasResult, LiftedCoreAliasLatest, LiftedCoreAliasReportedProposals, LiftedCoreAliasStartElection, LiftedCoreAliasAdoptTerm, LiftedCoreAliasGrantVote, LiftedCoreAliasDeliverVote, LiftedCoreAliasWinElection, LiftedCoreAliasMakeReport, LiftedCoreAliasDeliverReport, LiftedCoreAliasBuildRecovery, LiftedCoreAliasSendEntry, LiftedCoreAliasReceiveEntry, LiftedCoreAliasAckEntry, LiftedCoreAliasCopyProposalEntry, LiftedCoreAliasRetainProposal, LiftedCoreAliasAckProposal, LiftedCoreAliasDeliverAck, LiftedCoreAliasConfirmProposal, LiftedCoreAliasLearnConfirmation, LiftedCoreAliasCommitEntry, LiftedCoreAliasAdvertiseCommit, LiftedCoreAliasLearnCommit, LiftedCoreAliasActivate, LiftedCoreAliasCrash, LiftedCoreAliasRestart
   DEF AdministrativeNext, LiftedSafety!AdministrativeNext

THEOREM LiftedCoreAliasProtocolNext ==
    LiftedSafety!ProtocolNext = ProtocolNext
BY ONLY SMT, LiftedCoreAliasCreateEntry, LiftedCoreAliasCreateSuccessor, LiftedCoreAliasApplyEntry, LiftedCoreAliasAdministrativeNext
   DEF ProtocolNext, LiftedSafety!ProtocolNext
=============================================================================
