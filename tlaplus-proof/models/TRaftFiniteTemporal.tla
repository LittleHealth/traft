------------------------ MODULE TRaftFiniteTemporal ------------------------
EXTENDS TRaftControlTemporal, TRaftFiniteStartElection,
        TRaftFiniteAdoptTerm,
        TRaftFiniteGrantVote,
        TRaftFiniteDeliverVote,
        TRaftFiniteWinElection,
        TRaftFiniteMakeReport,
        TRaftFiniteDeliverReport,
        TRaftFiniteBuildRecovery,
        TRaftFiniteCreateEntry,
        TRaftFiniteCreateSuccessor,
        TRaftFiniteSendEntry,
        TRaftFiniteReceiveEntry,
        TRaftFiniteAckEntry,
        TRaftFiniteCopyProposalEntry,
        TRaftFiniteRetainProposal,
        TRaftFiniteAckProposal,
        TRaftFiniteDeliverAck,
        TRaftFiniteConfirmProposal,
        TRaftFiniteLearnConfirmation,
        TRaftFiniteCommitEntry,
        TRaftFiniteAdvertiseCommit,
        TRaftFiniteLearnCommit,
        TRaftFiniteActivate,
        TRaftFiniteApplyEntry,
        TRaftFiniteCrash,
        TRaftFiniteRestart

THEOREM FiniteLogInductiveStep ==
    ASSUME ControlInvariant, FiniteLogInvariant, Next
    PROVE FiniteLogInvariant'
<1>1. ControlInvariant /\ FiniteLogInvariant /\ Next
    OBVIOUS
<1> QED BY ONLY SMT, <1>1, StartElectionPreservesFiniteLogs,
        AdoptTermPreservesFiniteLogs,
        GrantVotePreservesFiniteLogs,
        DeliverVotePreservesFiniteLogs,
        WinElectionPreservesFiniteLogs,
        MakeReportPreservesFiniteLogs,
        DeliverReportPreservesFiniteLogs,
        BuildRecoveryPreservesFiniteLogs,
        CreateEntryPreservesFiniteLogs,
        CreateSuccessorPreservesFiniteLogs,
        SendEntryPreservesFiniteLogs,
        ReceiveEntryPreservesFiniteLogs,
        AckEntryPreservesFiniteLogs,
        CopyProposalEntryPreservesFiniteLogs,
        RetainProposalPreservesFiniteLogs,
        AckProposalPreservesFiniteLogs,
        DeliverAckPreservesFiniteLogs,
        ConfirmProposalPreservesFiniteLogs,
        LearnConfirmationPreservesFiniteLogs,
        CommitEntryPreservesFiniteLogs,
        AdvertiseCommitPreservesFiniteLogs,
        LearnCommitPreservesFiniteLogs,
        ActivatePreservesFiniteLogs,
        ApplyEntryPreservesFiniteLogs,
        CrashPreservesFiniteLogs,
        RestartPreservesFiniteLogs
    DEF Next, ProtocolNext, AdministrativeNext

THEOREM FiniteLogInvariantAlways == Spec => []FiniteLogInvariant
<1>1. Spec => []ControlInvariant
    BY ControlInvariantAlways
<1>2. Init => FiniteLogInvariant
    BY FiniteLogInitially
<1>3. ControlInvariant /\ FiniteLogInvariant /\ [Next]_vars => FiniteLogInvariant'
    BY SMT, FiniteLogInductiveStep, FiniteLogStuttering
       DEF FiniteLogVars, vars, protocolVars, observerVars
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
