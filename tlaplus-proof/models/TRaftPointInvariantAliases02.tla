---------------------- MODULE TRaftPointInvariantAliases02 ----------------------
EXTENDS TRaftPointInvariantAliases01

\* Local definition equalities between the same history substitutions.
\* Each equality and every imported theorem require independent checking.

THEOREM PointInvariantAliasCount ==
    \A L, p : PointLift!Count(L, p) = LiftedSafety!Count(L, p)
BY ONLY ZenonT(10), PointCoreAliasCount, LiftedCoreAliasCount

THEOREM PointInvariantAliasIndices ==
    PointLift!Indices = LiftedSafety!Indices
BY ONLY ZenonT(10), PointCoreAliasIndices, LiftedCoreAliasIndices

THEOREM PointInvariantAliasPartitions ==
    PointLift!Partitions = LiftedSafety!Partitions
BY ONLY ZenonT(10), PointCoreAliasPartitions, LiftedCoreAliasPartitions

THEOREM PointInvariantAliasEntries ==
    PointLift!Entries = LiftedSafety!Entries
BY ONLY ZenonT(10), PointCoreAliasEntries, LiftedCoreAliasEntries

THEOREM PointInvariantAliasMaxOr ==
    \A S, empty : PointLift!MaxOr(S, empty) = LiftedSafety!MaxOr(S, empty)
BY ONLY ZenonT(10), PointCoreAliasMaxOr, LiftedCoreAliasMaxOr

THEOREM PointInvariantAliasCur ==
    \A L : PointLift!Cur(L) = LiftedSafety!Cur(L)
BY ONLY ZenonT(10), PointCoreAliasCur, LiftedCoreAliasCur

THEOREM PointInvariantAliasLastIndex ==
    \A L : PointLift!LastIndex(L) = LiftedSafety!LastIndex(L)
BY ONLY ZenonT(10), PointCoreAliasLastIndex, LiftedCoreAliasLastIndex

THEOREM PointInvariantAliasLastTerm ==
    \A L : PointLift!LastTerm(L) = LiftedSafety!LastTerm(L)
BY ONLY ZenonT(10), PointCoreAliasLastTerm, LiftedCoreAliasLastTerm

THEOREM PointInvariantAliasSublog ==
    \A L : PointLift!Sublog(L) = LiftedSafety!Sublog(L)
BY ONLY ZenonT(10), PointInvariantAliasCur, PointInvariantAliasLastTerm, PointInvariantAliasPrefix, PointInvariantAliasResult, PointInvariantAliasTerms
   DEF PointLift!Sublog, LiftedSafety!Sublog

THEOREM PointInvariantAliasCanonicalShape ==
    PointLift!CanonicalShape = LiftedSafety!CanonicalShape
BY ONLY ZenonT(10), PointInvariantAliasCoherent, PointInvariantAliasContextSound, PointInvariantAliasCount, PointInvariantAliasEntries, PointInvariantAliasPartitions, PointInvariantAliasPrefix, PointInvariantAliasResult, PointInvariantAliasSublog, PointInvariantAliasTerms
   DEF PointLift!CanonicalShape, LiftedSafety!CanonicalShape

THEOREM PointInvariantAliasCanonicalViewLinks ==
    PointLift!CanonicalViewLinks = LiftedSafety!CanonicalViewLinks
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!CanonicalViewLinks, LiftedSafety!CanonicalViewLinks

THEOREM PointInvariantAliasCertifiedLogEntries ==
    \A V, P : PointLift!CertifiedLogEntries(V, P) = LiftedSafety!CertifiedLogEntries(V, P)
BY ONLY ZenonT(10), PointInvariantAliasResult
   DEF PointLift!CertifiedLogEntries, LiftedSafety!CertifiedLogEntries

THEOREM PointInvariantAliasCertifiedContexts ==
    \A E, V, P : PointLift!CertifiedContexts(E, V, P) = LiftedSafety!CertifiedContexts(E, V, P)
BY ONLY ZenonT(10), PointInvariantAliasCertifiedLogEntries
   DEF PointLift!CertifiedContexts, LiftedSafety!CertifiedContexts

THEOREM PointInvariantAliasHasClosedContext ==
    \A E, p, S : PointLift!HasClosedContext(E, p, S) = LiftedSafety!HasClosedContext(E, p, S)
BY ONLY ZenonT(10), PointInvariantAliasPart
   DEF PointLift!HasClosedContext, LiftedSafety!HasClosedContext

THEOREM PointInvariantAliasClosedPartitionOrigins ==
    \A H, E : PointLift!ClosedPartitionOrigins(H, E) = LiftedSafety!ClosedPartitionOrigins(H, E)
BY ONLY ZenonT(10), PointInvariantAliasHasClosedContext
   DEF PointLift!ClosedPartitionOrigins, LiftedSafety!ClosedPartitionOrigins

THEOREM PointInvariantAliasCertifiedPartitionHistory ==
    PointLift!CertifiedPartitionHistory = LiftedSafety!CertifiedPartitionHistory
BY ONLY ZenonT(10), PointInvariantAliasCertifiedContexts, PointInvariantAliasClosedPartitionOrigins
   DEF PointLift!CertifiedPartitionHistory, LiftedSafety!CertifiedPartitionHistory

THEOREM PointInvariantAliasNoReport ==
    PointLift!NoReport = LiftedSafety!NoReport
BY ONLY ZenonT(10), PointCoreAliasNoReport, LiftedCoreAliasNoReport

THEOREM PointInvariantAliasReporters ==
    \A c : PointLift!Reporters(c) = LiftedSafety!Reporters(c)
BY ONLY ZenonT(10), PointCoreAliasReporters, LiftedCoreAliasReporters

THEOREM PointInvariantAliasCollectedReportProvenance ==
    PointLift!CollectedReportProvenance = LiftedSafety!CollectedReportProvenance
BY ONLY ZenonT(10), PointInvariantAliasReporters
   DEF PointLift!CollectedReportProvenance, LiftedSafety!CollectedReportProvenance

THEOREM PointInvariantAliasCommitMessageEvidence ==
    PointLift!CommitMessageEvidence = LiftedSafety!CommitMessageEvidence
BY ONLY ZenonT(10)
   DEF PointLift!CommitMessageEvidence, LiftedSafety!CommitMessageEvidence

THEOREM PointInvariantAliasCommittedKnowledgeSound ==
    PointLift!CommittedKnowledgeSound = LiftedSafety!CommittedKnowledgeSound
BY ONLY ZenonT(10)
   DEF PointLift!CommittedKnowledgeSound, LiftedSafety!CommittedKnowledgeSound

THEOREM PointInvariantAliasConfirmationHasQuorum ==
    PointLift!ConfirmationHasQuorum = LiftedSafety!ConfirmationHasQuorum
BY ONLY ZenonT(10), PointInvariantAliasAck, PointInvariantAliasQuorum, PointInvariantAliasResult
   DEF PointLift!ConfirmationHasQuorum, LiftedSafety!ConfirmationHasQuorum

THEOREM PointInvariantAliasConfirmationSources ==
    PointLift!ConfirmationSources = LiftedSafety!ConfirmationSources
BY ONLY ZenonT(10)
   DEF PointLift!ConfirmationSources, LiftedSafety!ConfirmationSources

THEOREM PointInvariantAliasContextOrigins ==
    \A C, E : PointLift!ContextOrigins(C, E) = LiftedSafety!ContextOrigins(C, E)
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!ContextOrigins, LiftedSafety!ContextOrigins

THEOREM PointInvariantAliasNoProposal ==
    PointLift!NoProposal = LiftedSafety!NoProposal
BY ONLY ZenonT(10), PointCoreAliasNoProposal, LiftedCoreAliasNoProposal

THEOREM PointInvariantAliasPhases ==
    PointLift!Phases = LiftedSafety!Phases
BY ONLY ZenonT(10), PointCoreAliasPhases, LiftedCoreAliasPhases

THEOREM PointInvariantAliasControlShape ==
    PointLift!ControlShape = LiftedSafety!ControlShape
BY ONLY ZenonT(10), PointInvariantAliasNoProposal, PointInvariantAliasNoReport, PointInvariantAliasPhases
   DEF PointLift!ControlShape, LiftedSafety!ControlShape

THEOREM PointInvariantAliasOwnedEpochs ==
    \A S, T, W : PointLift!OwnedEpochs(S, T, W) = LiftedSafety!OwnedEpochs(S, T, W)
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!OwnedEpochs, LiftedSafety!OwnedEpochs

THEOREM PointInvariantAliasProposalProvenance ==
    PointLift!ProposalProvenance = LiftedSafety!ProposalProvenance
BY ONLY ZenonT(10), PointInvariantAliasOwnedEpochs
   DEF PointLift!ProposalProvenance, LiftedSafety!ProposalProvenance

THEOREM PointInvariantAliasRecoveryRequestProvenance ==
    PointLift!RecoveryRequestProvenance = LiftedSafety!RecoveryRequestProvenance
BY ONLY ZenonT(10), PointInvariantAliasOwnedEpochs
   DEF PointLift!RecoveryRequestProvenance, LiftedSafety!RecoveryRequestProvenance

=============================================================================
