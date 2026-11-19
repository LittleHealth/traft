---------------------- MODULE TRaftPointInvariantAliases04 ----------------------
EXTENDS TRaftPointInvariantAliases03

\* Local definition equalities between the same history substitutions.
\* Each equality and every imported theorem require independent checking.

THEOREM PointInvariantAliasPartitionHistoryOrigins ==
    PointLift!PartitionHistoryOrigins = LiftedSafety!PartitionHistoryOrigins
BY ONLY ZenonT(10), PointInvariantAliasPartitions, PointInvariantAliasTerms
   DEF PointLift!PartitionHistoryOrigins, LiftedSafety!PartitionHistoryOrigins

THEOREM PointInvariantAliasHistoryOriginInvariant ==
    PointLift!HistoryOriginInvariant = LiftedSafety!HistoryOriginInvariant
BY ONLY ZenonT(10), PointInvariantAliasAppliedEvidence, PointInvariantAliasAppliedPartitionOrigins, PointInvariantAliasPartitionHistoryOrigins
   DEF PointLift!HistoryOriginInvariant, LiftedSafety!HistoryOriginInvariant

THEOREM PointInvariantAliasHistoryPartitionCompleteness ==
    PointLift!HistoryPartitionCompleteness = LiftedSafety!HistoryPartitionCompleteness
BY ONLY ZenonT(10), PointInvariantAliasClosedPartitionOrigins
   DEF PointLift!HistoryPartitionCompleteness, LiftedSafety!HistoryPartitionCompleteness

THEOREM PointInvariantAliasInstalledEntriesHaveSource ==
    PointLift!InstalledEntriesHaveSource = LiftedSafety!InstalledEntriesHaveSource
BY ONLY ZenonT(10), PointInvariantAliasFormalEntriesFrom
   DEF PointLift!InstalledEntriesHaveSource, LiftedSafety!InstalledEntriesHaveSource

THEOREM PointInvariantAliasIssuedEntries ==
    PointLift!IssuedEntries = LiftedSafety!IssuedEntries
BY ONLY ZenonT(10)
   DEF PointLift!IssuedEntries, LiftedSafety!IssuedEntries

THEOREM PointInvariantAliasKnowledgeShape ==
    PointLift!KnowledgeShape = LiftedSafety!KnowledgeShape
BY ONLY ZenonT(10)
   DEF PointLift!KnowledgeShape, LiftedSafety!KnowledgeShape

THEOREM PointInvariantAliasKnowledgeInvariant ==
    PointLift!KnowledgeInvariant = LiftedSafety!KnowledgeInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckInboxOrigins, PointInvariantAliasCommitMessageEvidence, PointInvariantAliasCommittedKnowledgeSound, PointInvariantAliasConfirmationHasQuorum, PointInvariantAliasKnowledgeShape
   DEF PointLift!KnowledgeInvariant, LiftedSafety!KnowledgeInvariant

THEOREM PointInvariantAliasLeaderViewCertificates ==
    \A V, W : PointLift!LeaderViewCertificates(V, W) = LiftedSafety!LeaderViewCertificates(V, W)
BY ONLY ZenonT(10)
   DEF PointLift!LeaderViewCertificates, LiftedSafety!LeaderViewCertificates

THEOREM PointInvariantAliasPastLeaderViews ==
    \A V, T, R : PointLift!PastLeaderViews(V, T, R) = LiftedSafety!PastLeaderViews(V, T, R)
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!PastLeaderViews, LiftedSafety!PastLeaderViews

THEOREM PointInvariantAliasLeaderHistoryInvariant ==
    PointLift!LeaderHistoryInvariant = LiftedSafety!LeaderHistoryInvariant
BY ONLY ZenonT(10), PointInvariantAliasLeaderViewCertificates, PointInvariantAliasPastLeaderViews
   DEF PointLift!LeaderHistoryInvariant, LiftedSafety!LeaderHistoryInvariant

THEOREM PointInvariantAliasPossibleAckers ==
    \A t, e : PointLift!PossibleAckers(t, e) = LiftedSafety!PossibleAckers(t, e)
BY ONLY ZenonT(10), PointInvariantAliasEpochAckers
   DEF PointLift!PossibleAckers, LiftedSafety!PossibleAckers

THEOREM PointInvariantAliasMayChoose ==
    \A t, e : PointLift!MayChoose(t, e) = LiftedSafety!MayChoose(t, e)
BY ONLY ZenonT(10), PointInvariantAliasPossibleAckers, PointInvariantAliasQuorum
   DEF PointLift!MayChoose, LiftedSafety!MayChoose

THEOREM PointInvariantAliasRetainedProposalsActual ==
    PointLift!RetainedProposalsActual = LiftedSafety!RetainedProposalsActual
BY ONLY ZenonT(10)
   DEF PointLift!RetainedProposalsActual, LiftedSafety!RetainedProposalsActual

THEOREM PointInvariantAliasMessageSourceInvariant ==
    PointLift!MessageSourceInvariant = LiftedSafety!MessageSourceInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckSourceInvariant, PointInvariantAliasConfirmationSources, PointInvariantAliasRetainedProposalsActual
   DEF PointLift!MessageSourceInvariant, LiftedSafety!MessageSourceInvariant

THEOREM PointInvariantAliasOfferCountEvidence ==
    \A O, E, H : PointLift!OfferCountEvidence(O, E, H) = LiftedSafety!OfferCountEvidence(O, E, H)
BY ONLY ZenonT(10), PointInvariantAliasCardinality, PointInvariantAliasIsFiniteSet, PointInvariantAliasKnownBy, PointInvariantAliasPart
   DEF PointLift!OfferCountEvidence, LiftedSafety!OfferCountEvidence

THEOREM PointInvariantAliasOfferProvenance ==
    PointLift!OfferProvenance = LiftedSafety!OfferProvenance
BY ONLY ZenonT(10)
   DEF PointLift!OfferProvenance, LiftedSafety!OfferProvenance

THEOREM PointInvariantAliasReportContents ==
    \A m : PointLift!ReportContents(m) = LiftedSafety!ReportContents(m)
BY ONLY ZenonT(10), PointInvariantAliasResult
   DEF PointLift!ReportContents, LiftedSafety!ReportContents

THEOREM PointInvariantAliasRetainedContents ==
    \A r : PointLift!RetainedContents(r) = LiftedSafety!RetainedContents(r)
BY ONLY ZenonT(10), PointInvariantAliasResult
   DEF PointLift!RetainedContents, LiftedSafety!RetainedContents

THEOREM PointInvariantAliasPotentialCoverage ==
    PointLift!PotentialCoverage = LiftedSafety!PotentialCoverage
BY ONLY ZenonT(10), PointInvariantAliasMayChoose, PointInvariantAliasReportContents, PointInvariantAliasRetainedContents
   DEF PointLift!PotentialCoverage, LiftedSafety!PotentialCoverage

THEOREM PointInvariantAliasPotentialPreservation ==
    PointLift!PotentialPreservation = LiftedSafety!PotentialPreservation
BY ONLY ZenonT(10), PointInvariantAliasIssuedEntries, PointInvariantAliasMayChoose, PointInvariantAliasTerms
   DEF PointLift!PotentialPreservation, LiftedSafety!PotentialPreservation

THEOREM PointInvariantAliasReportFences ==
    PointLift!ReportFences = LiftedSafety!ReportFences
BY ONLY ZenonT(10), PointInvariantAliasQuorum, PointInvariantAliasReporters, PointInvariantAliasTerms
   DEF PointLift!ReportFences, LiftedSafety!ReportFences

THEOREM PointInvariantAliasTermAndVoteFacts ==
    PointLift!TermAndVoteFacts = LiftedSafety!TermAndVoteFacts
BY ONLY ZenonT(10), PointInvariantAliasQuorum, PointInvariantAliasTerms
   DEF PointLift!TermAndVoteFacts, LiftedSafety!TermAndVoteFacts

THEOREM PointInvariantAliasProposalRecords ==
    PointLift!ProposalRecords = LiftedSafety!ProposalRecords
BY ONLY ZenonT(10), PointCoreAliasProposalRecords, LiftedCoreAliasProposalRecords

THEOREM PointInvariantAliasTypeOK ==
    PointLift!TypeOK = LiftedSafety!TypeOK
BY ONLY ZenonT(10), PointCoreAliasTypeOK, LiftedCoreAliasTypeOK

THEOREM PointInvariantAliasRecoveryInvariant ==
    PointLift!RecoveryInvariant = LiftedSafety!RecoveryInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckOrigin, PointInvariantAliasCanonicalShape, PointInvariantAliasPotentialCoverage, PointInvariantAliasPotentialPreservation, PointInvariantAliasReportFences, PointInvariantAliasTermAndVoteFacts, PointInvariantAliasTypeOK
   DEF PointLift!RecoveryInvariant, LiftedSafety!RecoveryInvariant

THEOREM PointInvariantAliasRecoveryOriginFacts ==
    PointLift!RecoveryOriginFacts = LiftedSafety!RecoveryOriginFacts
BY ONLY ZenonT(10), PointInvariantAliasLastTerm, PointInvariantAliasResult, PointInvariantAliasTerms
   DEF PointLift!RecoveryOriginFacts, LiftedSafety!RecoveryOriginFacts

THEOREM PointInvariantAliasPreProvenanceInvariant ==
    PointLift!PreProvenanceInvariant = LiftedSafety!PreProvenanceInvariant
BY ONLY ZenonT(10), PointInvariantAliasControlInvariant, PointInvariantAliasDurabilityInvariant, PointInvariantAliasElectionInvariant, PointInvariantAliasFiniteLogInvariant, PointInvariantAliasRecoveryInvariant, PointInvariantAliasRecoveryOriginFacts
   DEF PointLift!PreProvenanceInvariant, LiftedSafety!PreProvenanceInvariant

THEOREM PointInvariantAliasRecoveryProposalBoundaries ==
    \A P : PointLift!RecoveryProposalBoundaries(P) = LiftedSafety!RecoveryProposalBoundaries(P)
BY ONLY ZenonT(10)
   DEF PointLift!RecoveryProposalBoundaries, LiftedSafety!RecoveryProposalBoundaries

THEOREM PointInvariantAliasPrefixEvidenceInvariant ==
    PointLift!PrefixEvidenceInvariant = LiftedSafety!PrefixEvidenceInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckPrefixEvidence, PointInvariantAliasActiveRecoveryCertificates, PointInvariantAliasEpochKnowledgeInvariant, PointInvariantAliasFollowerPrefixEvidence, PointInvariantAliasOfferCountEvidence, PointInvariantAliasRecoveryProposalBoundaries
   DEF PointLift!PrefixEvidenceInvariant, LiftedSafety!PrefixEvidenceInvariant

THEOREM PointInvariantAliasProofInvariant ==
    PointLift!ProofInvariant = LiftedSafety!ProofInvariant
BY ONLY ZenonT(10), PointInvariantAliasCanonicalDefinition, PointInvariantAliasCanonicalFinite, PointInvariantAliasCanonicalViewLinks, PointInvariantAliasCertifiedPartitionHistory, PointInvariantAliasContextOrigins, PointInvariantAliasEntryBoundaryCounts, PointInvariantAliasHistoryOriginInvariant, PointInvariantAliasHistoryPartitionCompleteness, PointInvariantAliasInstalledEntriesHaveSource, PointInvariantAliasKnowledgeInvariant, PointInvariantAliasLeaderHistoryInvariant, PointInvariantAliasMessageSourceInvariant, PointInvariantAliasOfferProvenance, PointInvariantAliasPreProvenanceInvariant, PointInvariantAliasPrefixEvidenceInvariant
   DEF PointLift!ProofInvariant, LiftedSafety!ProofInvariant

=============================================================================
