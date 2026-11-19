-------------------- MODULE TRaftBoundedProtocolRefinement -------------------
EXTENDS TRaftBoundedActionInstances

\* Physical projection only; the observer-history mapping remains separate.
InfinitePhysicalBehavior == Infinite!Init /\ [][Infinite!ProtocolNext]_protocolVars

THEOREM AdministrativeMessageDomainsIdentical ==
    /\ NoProposal = Infinite!NoProposal
    /\ \A c : Latest(ReportedProposals(c)) = Infinite!Latest(Infinite!ReportedProposals(c))
    /\ \A p : Result(p) = Infinite!Result(p)
BY DEF NoProposal, Infinite!NoProposal, NoReport, Infinite!NoReport,
       Latest, Infinite!Latest, Later, Infinite!Later,
       ReportedProposals, Infinite!ReportedProposals, Reporters, Infinite!Reporters,
       Result, Infinite!Result

THEOREM BoundedAdministrativeStepEmbeds ==
    AdministrativeNext => Infinite!AdministrativeNext
BY BoundedStartElectionEmbeds, BoundedAdoptTermEmbeds, BoundedGrantVoteEmbeds,
    BoundedDeliverVoteEmbeds, BoundedWinElectionEmbeds, BoundedMakeReportEmbeds,
    BoundedDeliverReportEmbeds, BoundedBuildRecoveryEmbeds, BoundedSendEntryEmbeds,
    BoundedReceiveEntryEmbeds, BoundedAckEntryEmbeds, BoundedCopyProposalEntryEmbeds,
    BoundedRetainProposalEmbeds, BoundedAckProposalEmbeds, BoundedDeliverAckEmbeds,
    BoundedConfirmProposalEmbeds, BoundedLearnConfirmationEmbeds, BoundedCommitEntryEmbeds,
    BoundedAdvertiseCommitEmbeds, BoundedLearnCommitEmbeds, BoundedActivateEmbeds,
    BoundedCrashEmbeds, BoundedRestartEmbeds, IdentifierDomainsEmbed,
    AdministrativeMessageDomainsIdentical, ZenonT(5)
    DEF AdministrativeNext, Infinite!AdministrativeNext

THEOREM BoundedProtocolStepEmbeds == ProtocolNext => Infinite!ProtocolNext
BY BoundedAdministrativeStepEmbeds, BoundedCreateEntryEmbeds, BoundedCreateSuccessorEmbeds,
   BoundedApplyEntryEmbeds, ZenonT(5)
   DEF ProtocolNext, Infinite!ProtocolNext

THEOREM BoundedPhysicalBehaviorRefinesUnbounded == Spec => InfinitePhysicalBehavior
<1>1. Init => Infinite!Init
    BY BoundedInitializationEmbeds
<1>2. [Next]_vars => [Infinite!ProtocolNext]_protocolVars
    BY BoundedProtocolStepEmbeds DEF Next, vars
<1> QED BY PTL, <1>1, <1>2 DEF Spec, InfinitePhysicalBehavior
=============================================================================
