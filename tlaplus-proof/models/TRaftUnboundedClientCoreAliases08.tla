-------------------- MODULE TRaftUnboundedClientCoreAliases08 --------------------
EXTENDS TRaftUnboundedClientCoreAliases07b

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasApplyEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!ApplyEntry(aliasArg1, aliasArg2) = ApplyEntry(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasPrefix
   DEF ApplyEntry, UnboundedClient!ApplyEntry

THEOREM UnboundedClientCoreAliasCrash ==
    \A aliasArg1 : UnboundedClient!Crash(aliasArg1) = Crash(aliasArg1)
BY ONLY SMT, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasEmptyReports
   DEF Crash, UnboundedClient!Crash

THEOREM UnboundedClientCoreAliasRestart ==
    \A aliasArg1 : UnboundedClient!Restart(aliasArg1) = Restart(aliasArg1)
BY ONLY SMT
   DEF Restart, UnboundedClient!Restart

THEOREM UnboundedClientCoreAliasAdministrativeNext ==
    UnboundedClient!AdministrativeNext = AdministrativeNext
BY ONLY SMT, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasResult, UnboundedClientCoreAliasLatest, UnboundedClientCoreAliasReportedProposals, UnboundedClientCoreAliasStartElection, UnboundedClientCoreAliasAdoptTerm, UnboundedClientCoreAliasGrantVote, UnboundedClientCoreAliasDeliverVote, UnboundedClientCoreAliasWinElection, UnboundedClientCoreAliasMakeReport, UnboundedClientCoreAliasDeliverReport, UnboundedClientCoreAliasBuildRecovery, UnboundedClientCoreAliasSendEntry, UnboundedClientCoreAliasReceiveEntry, UnboundedClientCoreAliasAckEntry, UnboundedClientCoreAliasCopyProposalEntry, UnboundedClientCoreAliasRetainProposal, UnboundedClientCoreAliasAckProposal, UnboundedClientCoreAliasDeliverAck, UnboundedClientCoreAliasConfirmProposal, UnboundedClientCoreAliasLearnConfirmation, UnboundedClientCoreAliasCommitEntry, UnboundedClientCoreAliasAdvertiseCommit, UnboundedClientCoreAliasLearnCommit, UnboundedClientCoreAliasActivate, UnboundedClientCoreAliasCrash, UnboundedClientCoreAliasRestart
   DEF AdministrativeNext, UnboundedClient!AdministrativeNext

THEOREM UnboundedClientCoreAliasProtocolNext ==
    UnboundedClient!ProtocolNext = ProtocolNext
BY ONLY SMT, UnboundedClientCoreAliasCreateEntry, UnboundedClientCoreAliasCreateSuccessor, UnboundedClientCoreAliasApplyEntry, UnboundedClientCoreAliasAdministrativeNext, UnboundedClientDomains
   DEF ProtocolNext, UnboundedClient!ProtocolNext
=============================================================================
