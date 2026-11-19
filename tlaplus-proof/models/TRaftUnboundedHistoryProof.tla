----------------------- MODULE TRaftUnboundedHistoryProof --------------------
EXTENDS TRaftUnbounded, TLAPS
USE UnboundedParameters DEF UnboundedParameters, ParameterAssumptions, SentinelSeparation

VARIABLE canonical
HistoryInstance == INSTANCE TRaftHistoryRefinementProof
    WITH MaxTerm <- (-1), MaxIndex <- (-1), MaxPartition <- (-1),
         MutDropPending <- FALSE, MutSkipRecoveryUnion <- FALSE,
         MutEarlyPublish <- FALSE, MutNoCommitQuorum <- FALSE, MutSkipBoundaryCommit <- FALSE

\* This is the actual unbounded module's history lifting. It is distinct
\* from the still-required finite-to-unbounded observer-history mapping.
THEOREM UnboundedInstanceSpecificationIdentity == Spec <=> HistoryInstance!Spec
BY
   DEF NoNode, HistoryInstance!NoNode, NoProposal, HistoryInstance!NoProposal, NoReport,
       HistoryInstance!NoReport, Roles, HistoryInstance!Roles, Phases, HistoryInstance!Phases,
       NoBound, HistoryInstance!NoBound, Terms, HistoryInstance!Terms, Indices,
       HistoryInstance!Indices, Partitions, HistoryInstance!Partitions, Entries,
       HistoryInstance!Entries, ProposalRecords, HistoryInstance!ProposalRecords, MaxOr,
       HistoryInstance!MaxOr, Cur, HistoryInstance!Cur, LastIndex, HistoryInstance!LastIndex,
       Part, HistoryInstance!Part, Prefix, HistoryInstance!Prefix, Count, HistoryInstance!Count,
       ClosedPrefix, HistoryInstance!ClosedPrefix, LastTerm, HistoryInstance!LastTerm, Origin,
       HistoryInstance!Origin, Rank, HistoryInstance!Rank, AtLeast, HistoryInstance!AtLeast,
       Quorum, HistoryInstance!Quorum, Coherent, HistoryInstance!Coherent, Entry,
       HistoryInstance!Entry, Proposal, HistoryInstance!Proposal, Result, HistoryInstance!Result,
       Later, HistoryInstance!Later, Latest, HistoryInstance!Latest, Ack, HistoryInstance!Ack,
       protocolVars, HistoryInstance!protocolVars, observerVars, HistoryInstance!observerVars,
       vars, HistoryInstance!vars, EmptyReports, HistoryInstance!EmptyReports, Reporters,
       HistoryInstance!Reporters, ReportedProposals, HistoryInstance!ReportedProposals,
       ReportedEntries, HistoryInstance!ReportedEntries, Recovered, HistoryInstance!Recovered,
       Aligned, HistoryInstance!Aligned, MessageAckers, HistoryInstance!MessageAckers, Ackers,
       HistoryInstance!Ackers, ProposalAckers, HistoryInstance!ProposalAckers, Publish,
       HistoryInstance!Publish, NormalMessage, HistoryInstance!NormalMessage, CanReceive,
       HistoryInstance!CanReceive, Init, HistoryInstance!Init, StartElection,
       HistoryInstance!StartElection, AdoptTerm, HistoryInstance!AdoptTerm, GrantVote,
       HistoryInstance!GrantVote, DeliverVote, HistoryInstance!DeliverVote, WinElection,
       HistoryInstance!WinElection, MakeReport, HistoryInstance!MakeReport, DeliverReport,
       HistoryInstance!DeliverReport, BuildRecovery, HistoryInstance!BuildRecovery, CreateEntry,
       HistoryInstance!CreateEntry, CreateSuccessor, HistoryInstance!CreateSuccessor, SendEntry,
       HistoryInstance!SendEntry, ReceiveEntry, HistoryInstance!ReceiveEntry, AckEntry,
       HistoryInstance!AckEntry, CopyProposalEntry, HistoryInstance!CopyProposalEntry,
       RetainProposal, HistoryInstance!RetainProposal, AckProposal, HistoryInstance!AckProposal,
       DeliverAck, HistoryInstance!DeliverAck, ConfirmProposal, HistoryInstance!ConfirmProposal,
       LearnConfirmation, HistoryInstance!LearnConfirmation, CommitEntry,
       HistoryInstance!CommitEntry, AdvertiseCommit, HistoryInstance!AdvertiseCommit,
       LearnCommit, HistoryInstance!LearnCommit, Activate, HistoryInstance!Activate, ApplyEntry,
       HistoryInstance!ApplyEntry, Crash, HistoryInstance!Crash, Restart,
       HistoryInstance!Restart, AdministrativeNext, HistoryInstance!AdministrativeNext,
       ProtocolNext, HistoryInstance!ProtocolNext, Evidence, HistoryInstance!Evidence,
       EvidenceEntries, HistoryInstance!EvidenceEntries, Observe, HistoryInstance!Observe, Next,
       HistoryInstance!Next, Spec, HistoryInstance!Spec, IsFiniteSet,
       HistoryInstance!IsFiniteSet, Cardinality, HistoryInstance!Cardinality

THEOREM UnboundedInstanceParameters ==
    HistoryInstance!ParameterAssumptions /\ HistoryInstance!SentinelSeparation
BY ParameterAssumptions, SentinelSeparation
   DEF NoNode, HistoryInstance!NoNode, NoProposal, HistoryInstance!NoProposal, NoReport,
       HistoryInstance!NoReport, Roles, HistoryInstance!Roles, Phases, HistoryInstance!Phases,
       NoBound, HistoryInstance!NoBound, Terms, HistoryInstance!Terms, Indices,
       HistoryInstance!Indices, Partitions, HistoryInstance!Partitions, Entries,
       HistoryInstance!Entries, ProposalRecords, HistoryInstance!ProposalRecords, MaxOr,
       HistoryInstance!MaxOr, Cur, HistoryInstance!Cur, LastIndex, HistoryInstance!LastIndex,
       Part, HistoryInstance!Part, Prefix, HistoryInstance!Prefix, Count, HistoryInstance!Count,
       ClosedPrefix, HistoryInstance!ClosedPrefix, LastTerm, HistoryInstance!LastTerm, Origin,
       HistoryInstance!Origin, Rank, HistoryInstance!Rank, AtLeast, HistoryInstance!AtLeast,
       Quorum, HistoryInstance!Quorum, Coherent, HistoryInstance!Coherent, Entry,
       HistoryInstance!Entry, Proposal, HistoryInstance!Proposal, Result, HistoryInstance!Result,
       Later, HistoryInstance!Later, Latest, HistoryInstance!Latest, Ack, HistoryInstance!Ack,
       protocolVars, HistoryInstance!protocolVars, observerVars, HistoryInstance!observerVars,
       vars, HistoryInstance!vars, EmptyReports, HistoryInstance!EmptyReports, Reporters,
       HistoryInstance!Reporters, ReportedProposals, HistoryInstance!ReportedProposals,
       ReportedEntries, HistoryInstance!ReportedEntries, Recovered, HistoryInstance!Recovered,
       Aligned, HistoryInstance!Aligned, MessageAckers, HistoryInstance!MessageAckers, Ackers,
       HistoryInstance!Ackers, ProposalAckers, HistoryInstance!ProposalAckers, Publish,
       HistoryInstance!Publish, NormalMessage, HistoryInstance!NormalMessage, CanReceive,
       HistoryInstance!CanReceive, Init, HistoryInstance!Init, StartElection,
       HistoryInstance!StartElection, AdoptTerm, HistoryInstance!AdoptTerm, GrantVote,
       HistoryInstance!GrantVote, DeliverVote, HistoryInstance!DeliverVote, WinElection,
       HistoryInstance!WinElection, MakeReport, HistoryInstance!MakeReport, DeliverReport,
       HistoryInstance!DeliverReport, BuildRecovery, HistoryInstance!BuildRecovery, CreateEntry,
       HistoryInstance!CreateEntry, CreateSuccessor, HistoryInstance!CreateSuccessor, SendEntry,
       HistoryInstance!SendEntry, ReceiveEntry, HistoryInstance!ReceiveEntry, AckEntry,
       HistoryInstance!AckEntry, CopyProposalEntry, HistoryInstance!CopyProposalEntry,
       RetainProposal, HistoryInstance!RetainProposal, AckProposal, HistoryInstance!AckProposal,
       DeliverAck, HistoryInstance!DeliverAck, ConfirmProposal, HistoryInstance!ConfirmProposal,
       LearnConfirmation, HistoryInstance!LearnConfirmation, CommitEntry,
       HistoryInstance!CommitEntry, AdvertiseCommit, HistoryInstance!AdvertiseCommit,
       LearnCommit, HistoryInstance!LearnCommit, Activate, HistoryInstance!Activate, ApplyEntry,
       HistoryInstance!ApplyEntry, Crash, HistoryInstance!Crash, Restart,
       HistoryInstance!Restart, AdministrativeNext, HistoryInstance!AdministrativeNext,
       ProtocolNext, HistoryInstance!ProtocolNext, Evidence, HistoryInstance!Evidence,
       EvidenceEntries, HistoryInstance!EvidenceEntries, Observe, HistoryInstance!Observe, Next,
       HistoryInstance!Next, Spec, HistoryInstance!Spec, IsFiniteSet,
       HistoryInstance!IsFiniteSet, Cardinality, HistoryInstance!Cardinality,
       ParameterAssumptions, SentinelSeparation,
       HistoryInstance!ParameterAssumptions, HistoryInstance!SentinelSeparation

THEOREM UnboundedHistoryLifting ==
    Spec => HistoryInstance!LiftedSpec(HistoryInstance!DerivedCanonical)
BY ONLY HistoryInstance!CoreAndHistoryRefinement, UnboundedInstanceSpecificationIdentity,
   UnboundedInstanceParameters

THEOREM UnboundedIdentifierDomains ==
    Terms = Nat /\ Indices = Nat \ {0} /\ Partitions = Nat
BY SMT DEF Terms, Indices, Partitions
=============================================================================
