---------------------- MODULE TRaftBoundedActionInstances --------------------
EXTENDS TRaftCore, TLAPS
USE ParameterAssumptions DEF ParameterAssumptions
Infinite == INSTANCE TRaftCore WITH MaxTerm <- (-1), MaxIndex <- (-1), MaxPartition <- (-1)

THEOREM IdentifierDomainsEmbed ==
    Terms \subseteq Infinite!Terms /\ Indices \subseteq Infinite!Indices
    /\ Partitions \subseteq Infinite!Partitions
BY SMT DEF Infinite!Terms, Infinite!Indices, Infinite!Partitions

THEOREM BoundedInitializationEmbeds == Init => Infinite!Init
BY ONLY ZenonT(5)
    DEF EmptyReports, Infinite!EmptyReports, Init, Infinite!Init, NoNode, Infinite!NoNode,
        NoProposal, Infinite!NoProposal, NoReport, Infinite!NoReport, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedStartElectionEmbeds ==
    ASSUME NEW c, StartElection(c)
    PROVE Infinite!StartElection(c)
<1>1. StartElection(c)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF EmptyReports, Infinite!EmptyReports, NoProposal, Infinite!NoProposal, NoReport,
        Infinite!NoReport, StartElection, Infinite!StartElection, IsFiniteSet, Infinite!IsFiniteSet,
        Cardinality, Infinite!Cardinality

THEOREM BoundedAdoptTermEmbeds ==
    ASSUME NEW r, NEW t, AdoptTerm(r, t)
    PROVE Infinite!AdoptTerm(r, t)
<1>1. AdoptTerm(r, t)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF AdoptTerm, Infinite!AdoptTerm, EmptyReports, Infinite!EmptyReports, NoNode, Infinite!NoNode,
        NoProposal, Infinite!NoProposal, NoReport, Infinite!NoReport, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedGrantVoteEmbeds ==
    ASSUME NEW r, NEW req, GrantVote(r, req)
    PROVE Infinite!GrantVote(r, req)
<1>1. GrantVote(r, req)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF AtLeast, Infinite!AtLeast, Count, Infinite!Count, Cur, Infinite!Cur, GrantVote,
        Infinite!GrantVote, LastIndex, Infinite!LastIndex, LastTerm, Infinite!LastTerm, MaxOr,
        Infinite!MaxOr, NoNode, Infinite!NoNode, Part, Infinite!Part, Rank, Infinite!Rank,
        IsFiniteSet, Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedDeliverVoteEmbeds ==
    ASSUME NEW c, NEW m, DeliverVote(c, m)
    PROVE Infinite!DeliverVote(c, m)
<1>1. DeliverVote(c, m)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF DeliverVote, Infinite!DeliverVote, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedWinElectionEmbeds ==
    ASSUME NEW c, WinElection(c)
    PROVE Infinite!WinElection(c)
<1>1. WinElection(c)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Quorum, Infinite!Quorum, WinElection, Infinite!WinElection, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedMakeReportEmbeds ==
    ASSUME NEW r, NEW req, MakeReport(r, req)
    PROVE Infinite!MakeReport(r, req)
<1>1. MakeReport(r, req)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF MakeReport, Infinite!MakeReport, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedDeliverReportEmbeds ==
    ASSUME NEW c, NEW m, DeliverReport(c, m)
    PROVE Infinite!DeliverReport(c, m)
<1>1. DeliverReport(c, m)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF DeliverReport, Infinite!DeliverReport, NoReport, Infinite!NoReport, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedBuildRecoveryEmbeds ==
    ASSUME NEW c, NEW selected, BuildRecovery(c, selected)
    PROVE Infinite!BuildRecovery(c, selected)
<1>1. BuildRecovery(c, selected)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF BuildRecovery, Infinite!BuildRecovery, Count, Infinite!Count, Cur, Infinite!Cur, Entry,
        Infinite!Entry, LastIndex, Infinite!LastIndex, Later, Infinite!Later, Latest,
        Infinite!Latest, MaxOr, Infinite!MaxOr, NoProposal, Infinite!NoProposal, NoReport,
        Infinite!NoReport, Part, Infinite!Part, Proposal, Infinite!Proposal, Quorum,
        Infinite!Quorum, Recovered, Infinite!Recovered, ReportedEntries, Infinite!ReportedEntries,
        ReportedProposals, Infinite!ReportedProposals, Reporters, Infinite!Reporters, Result,
        Infinite!Result, IsFiniteSet, Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedCreateEntryEmbeds ==
    ASSUME NEW c, NEW v, CreateEntry(c, v)
    PROVE Infinite!CreateEntry(c, v)
<1>1. CreateEntry(c, v)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Aligned, Infinite!Aligned, Count, Infinite!Count, CreateEntry, Infinite!CreateEntry, Cur,
        Infinite!Cur, Entry, Infinite!Entry, LastIndex, Infinite!LastIndex, MaxOr, Infinite!MaxOr,
        Origin, Infinite!Origin, Part, Infinite!Part, IsFiniteSet, Infinite!IsFiniteSet,
        Cardinality, Infinite!Cardinality

THEOREM BoundedCreateSuccessorEmbeds ==
    ASSUME NEW c, NEW v, NEW k, CreateSuccessor(c, v, k)
    PROVE Infinite!CreateSuccessor(c, v, k)
<1>1. CreateSuccessor(c, v, k)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Aligned, Infinite!Aligned, Count, Infinite!Count, CreateSuccessor, Infinite!CreateSuccessor,
        Cur, Infinite!Cur, Entry, Infinite!Entry, LastIndex, Infinite!LastIndex, MaxOr,
        Infinite!MaxOr, Part, Infinite!Part, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedSendEntryEmbeds ==
    ASSUME NEW c, NEW e, SendEntry(c, e)
    PROVE Infinite!SendEntry(c, e)
<1>1. SendEntry(c, e)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Count, Infinite!Count, NormalMessage, Infinite!NormalMessage, Part, Infinite!Part,
        SendEntry, Infinite!SendEntry, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedReceiveEntryEmbeds ==
    ASSUME NEW r, NEW o, ReceiveEntry(r, o)
    PROVE Infinite!ReceiveEntry(r, o)
<1>1. ReceiveEntry(r, o)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Aligned, Infinite!Aligned, CanReceive, Infinite!CanReceive, Count, Infinite!Count, Cur,
        Infinite!Cur, MaxOr, Infinite!MaxOr, Origin, Infinite!Origin, Part, Infinite!Part,
        ReceiveEntry, Infinite!ReceiveEntry, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedAckEntryEmbeds ==
    ASSUME NEW r, NEW o, AckEntry(r, o)
    PROVE Infinite!AckEntry(r, o)
<1>1. AckEntry(r, o)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Ack, Infinite!Ack, AckEntry, Infinite!AckEntry, IsFiniteSet, Infinite!IsFiniteSet,
        Cardinality, Infinite!Cardinality

THEOREM BoundedCopyProposalEntryEmbeds ==
    ASSUME NEW r, NEW source, NEW p, NEW e, CopyProposalEntry(r, source, p, e)
    PROVE Infinite!CopyProposalEntry(r, source, p, e)
<1>1. CopyProposalEntry(r, source, p, e)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF CopyProposalEntry, Infinite!CopyProposalEntry, Result, Infinite!Result, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedRetainProposalEmbeds ==
    ASSUME NEW r, NEW p, RetainProposal(r, p)
    PROVE Infinite!RetainProposal(r, p)
<1>1. RetainProposal(r, p)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Result, Infinite!Result, RetainProposal, Infinite!RetainProposal, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedAckProposalEmbeds ==
    ASSUME NEW r, NEW p, AckProposal(r, p)
    PROVE Infinite!AckProposal(r, p)
<1>1. AckProposal(r, p)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Ack, Infinite!Ack, AckProposal, Infinite!AckProposal, Result, Infinite!Result, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedDeliverAckEmbeds ==
    ASSUME NEW c, NEW m, DeliverAck(c, m)
    PROVE Infinite!DeliverAck(c, m)
<1>1. DeliverAck(c, m)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF DeliverAck, Infinite!DeliverAck, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedConfirmProposalEmbeds ==
    ASSUME NEW c, ConfirmProposal(c)
    PROVE Infinite!ConfirmProposal(c)
<1>1. ConfirmProposal(c)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Ack, Infinite!Ack, ConfirmProposal, Infinite!ConfirmProposal, NoProposal,
        Infinite!NoProposal, ProposalAckers, Infinite!ProposalAckers, Publish, Infinite!Publish,
        Quorum, Infinite!Quorum, Result, Infinite!Result, IsFiniteSet, Infinite!IsFiniteSet,
        Cardinality, Infinite!Cardinality

THEOREM BoundedLearnConfirmationEmbeds ==
    ASSUME NEW r, NEW p, LearnConfirmation(r, p)
    PROVE Infinite!LearnConfirmation(r, p)
<1>1. LearnConfirmation(r, p)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF LearnConfirmation, Infinite!LearnConfirmation, Publish, Infinite!Publish, Result,
        Infinite!Result, IsFiniteSet, Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedCommitEntryEmbeds ==
    ASSUME NEW c, NEW e, CommitEntry(c, e)
    PROVE Infinite!CommitEntry(c, e)
<1>1. CommitEntry(c, e)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Ackers, Infinite!Ackers, CommitEntry, Infinite!CommitEntry, MessageAckers,
        Infinite!MessageAckers, Prefix, Infinite!Prefix, Quorum, Infinite!Quorum, IsFiniteSet,
        Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedAdvertiseCommitEmbeds ==
    ASSUME NEW c, NEW e, AdvertiseCommit(c, e)
    PROVE Infinite!AdvertiseCommit(c, e)
<1>1. AdvertiseCommit(c, e)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF AdvertiseCommit, Infinite!AdvertiseCommit, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedLearnCommitEmbeds ==
    ASSUME NEW r, NEW m, LearnCommit(r, m)
    PROVE Infinite!LearnCommit(r, m)
<1>1. LearnCommit(r, m)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF LearnCommit, Infinite!LearnCommit, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedActivateEmbeds ==
    ASSUME NEW c, Activate(c)
    PROVE Infinite!Activate(c)
<1>1. Activate(c)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Activate, Infinite!Activate, NoProposal, Infinite!NoProposal, Result, Infinite!Result,
        IsFiniteSet, Infinite!IsFiniteSet, Cardinality, Infinite!Cardinality

THEOREM BoundedApplyEntryEmbeds ==
    ASSUME NEW r, NEW e, ApplyEntry(r, e)
    PROVE Infinite!ApplyEntry(r, e)
<1>1. ApplyEntry(r, e)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF ApplyEntry, Infinite!ApplyEntry, Prefix, Infinite!Prefix, IsFiniteSet, Infinite!IsFiniteSet,
        Cardinality, Infinite!Cardinality

THEOREM BoundedCrashEmbeds ==
    ASSUME NEW r, Crash(r)
    PROVE Infinite!Crash(r)
<1>1. Crash(r)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Crash, Infinite!Crash, EmptyReports, Infinite!EmptyReports, NoProposal, Infinite!NoProposal,
        NoReport, Infinite!NoReport, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

THEOREM BoundedRestartEmbeds ==
    ASSUME NEW r, Restart(r)
    PROVE Infinite!Restart(r)
<1>1. Restart(r)
    OBVIOUS
<1> QED BY ONLY IdentifierDomainsEmbed, <1>1, ZenonT(5)
    DEF Restart, Infinite!Restart, IsFiniteSet, Infinite!IsFiniteSet, Cardinality,
        Infinite!Cardinality

=============================================================================
