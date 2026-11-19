-------------------- MODULE TRaftUnboundedCoreAliases08 --------------------
EXTENDS TRaftUnboundedCoreAliases07b

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasApplyEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!ApplyEntry(aliasArg1, aliasArg2) = ApplyEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasPrefix
   DEF ApplyEntry, UnboundedCore!ApplyEntry

THEOREM UnboundedCoreAliasCrash ==
    \A aliasArg1 : UnboundedCore!Crash(aliasArg1) = Crash(aliasArg1)
BY ONLY SMT, UnboundedCoreAliasNoProposal, UnboundedCoreAliasEmptyReports
   DEF Crash, UnboundedCore!Crash

THEOREM UnboundedCoreAliasRestart ==
    \A aliasArg1 : UnboundedCore!Restart(aliasArg1) = Restart(aliasArg1)
BY ONLY SMT
   DEF Restart, UnboundedCore!Restart

THEOREM UnboundedCoreAliasAdministrativeNext ==
    UnboundedCore!AdministrativeNext = AdministrativeNext
BY ONLY SMT, UnboundedCoreAliasNoProposal, UnboundedCoreAliasTerms, UnboundedCoreAliasResult, UnboundedCoreAliasLatest, UnboundedCoreAliasReportedProposals, UnboundedCoreAliasStartElection, UnboundedCoreAliasAdoptTerm, UnboundedCoreAliasGrantVote, UnboundedCoreAliasDeliverVote, UnboundedCoreAliasWinElection, UnboundedCoreAliasMakeReport, UnboundedCoreAliasDeliverReport, UnboundedCoreAliasBuildRecovery, UnboundedCoreAliasSendEntry, UnboundedCoreAliasReceiveEntry, UnboundedCoreAliasAckEntry, UnboundedCoreAliasCopyProposalEntry, UnboundedCoreAliasRetainProposal, UnboundedCoreAliasAckProposal, UnboundedCoreAliasDeliverAck, UnboundedCoreAliasConfirmProposal, UnboundedCoreAliasLearnConfirmation, UnboundedCoreAliasCommitEntry, UnboundedCoreAliasAdvertiseCommit, UnboundedCoreAliasLearnCommit, UnboundedCoreAliasActivate, UnboundedCoreAliasCrash, UnboundedCoreAliasRestart
   DEF AdministrativeNext, UnboundedCore!AdministrativeNext

THEOREM UnboundedCoreAliasProtocolNext ==
    UnboundedCore!ProtocolNext = ProtocolNext
BY ONLY SMT, UnboundedCoreAliasCreateEntry, UnboundedCoreAliasCreateSuccessor, UnboundedCoreAliasApplyEntry, UnboundedCoreAliasAdministrativeNext
   DEF ProtocolNext, UnboundedCore!ProtocolNext
=============================================================================
