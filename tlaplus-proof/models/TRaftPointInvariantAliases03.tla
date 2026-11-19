---------------------- MODULE TRaftPointInvariantAliases03 ----------------------
EXTENDS TRaftPointInvariantAliases02

\* Local definition equalities between the same history substitutions.
\* Each equality and every imported theorem require independent checking.

THEOREM PointInvariantAliasReportProvenance ==
    PointLift!ReportProvenance = LiftedSafety!ReportProvenance
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!ReportProvenance, LiftedSafety!ReportProvenance

THEOREM PointInvariantAliasUnusedProposalEpoch ==
    PointLift!UnusedProposalEpoch = LiftedSafety!UnusedProposalEpoch
BY ONLY ZenonT(10)
   DEF PointLift!UnusedProposalEpoch, LiftedSafety!UnusedProposalEpoch

THEOREM PointInvariantAliasControlInvariant ==
    PointLift!ControlInvariant = LiftedSafety!ControlInvariant
BY ONLY ZenonT(10), PointInvariantAliasCollectedReportProvenance, PointInvariantAliasControlShape, PointInvariantAliasProposalProvenance, PointInvariantAliasRecoveryRequestProvenance, PointInvariantAliasReportProvenance, PointInvariantAliasUnusedProposalEpoch
   DEF PointLift!ControlInvariant, LiftedSafety!ControlInvariant

THEOREM PointInvariantAliasFormalShape ==
    PointLift!FormalShape = LiftedSafety!FormalShape
BY ONLY ZenonT(10)
   DEF PointLift!FormalShape, LiftedSafety!FormalShape

THEOREM PointInvariantAliasFormalStored ==
    PointLift!FormalStored = LiftedSafety!FormalStored
BY ONLY ZenonT(10)
   DEF PointLift!FormalStored, LiftedSafety!FormalStored

THEOREM PointInvariantAliasRetainedShape ==
    PointLift!RetainedShape = LiftedSafety!RetainedShape
BY ONLY ZenonT(10)
   DEF PointLift!RetainedShape, LiftedSafety!RetainedShape

THEOREM PointInvariantAliasRetainedStored ==
    PointLift!RetainedStored = LiftedSafety!RetainedStored
BY ONLY ZenonT(10), PointInvariantAliasResult
   DEF PointLift!RetainedStored, LiftedSafety!RetainedStored

THEOREM PointInvariantAliasStorageShape ==
    PointLift!StorageShape = LiftedSafety!StorageShape
BY ONLY ZenonT(10)
   DEF PointLift!StorageShape, LiftedSafety!StorageShape

THEOREM PointInvariantAliasDurableData ==
    PointLift!DurableData = LiftedSafety!DurableData
BY ONLY ZenonT(10), PointInvariantAliasFormalShape, PointInvariantAliasFormalStored, PointInvariantAliasRetainedShape, PointInvariantAliasRetainedStored, PointInvariantAliasStorageShape
   DEF PointLift!DurableData, LiftedSafety!DurableData

THEOREM PointInvariantAliasDurabilityInvariant ==
    PointLift!DurabilityInvariant = LiftedSafety!DurabilityInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckDurability, PointInvariantAliasAckSendersValid, PointInvariantAliasDurableData
   DEF PointLift!DurabilityInvariant, LiftedSafety!DurabilityInvariant

THEOREM PointInvariantAliasElectionBallotFacts ==
    PointLift!ElectionBallotFacts = LiftedSafety!ElectionBallotFacts
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!ElectionBallotFacts, LiftedSafety!ElectionBallotFacts

THEOREM PointInvariantAliasElectionInboxFacts ==
    PointLift!ElectionInboxFacts = LiftedSafety!ElectionInboxFacts
BY ONLY ZenonT(10)
   DEF PointLift!ElectionInboxFacts, LiftedSafety!ElectionInboxFacts

THEOREM PointInvariantAliasElectionRequestFacts ==
    PointLift!ElectionRequestFacts = LiftedSafety!ElectionRequestFacts
BY ONLY ZenonT(10), PointInvariantAliasTerms
   DEF PointLift!ElectionRequestFacts, LiftedSafety!ElectionRequestFacts

THEOREM PointInvariantAliasNoNode ==
    PointLift!NoNode = LiftedSafety!NoNode
BY ONLY ZenonT(10), PointCoreAliasNoNode, LiftedCoreAliasNoNode

THEOREM PointInvariantAliasRoles ==
    PointLift!Roles = LiftedSafety!Roles
BY ONLY ZenonT(10), PointCoreAliasRoles, LiftedCoreAliasRoles

THEOREM PointInvariantAliasElectionTypes ==
    PointLift!ElectionTypes = LiftedSafety!ElectionTypes
BY ONLY ZenonT(10), PointInvariantAliasNoNode, PointInvariantAliasRoles, PointInvariantAliasTerms
   DEF PointLift!ElectionTypes, LiftedSafety!ElectionTypes

THEOREM PointInvariantAliasElectionWinnerFacts ==
    PointLift!ElectionWinnerFacts = LiftedSafety!ElectionWinnerFacts
BY ONLY ZenonT(10), PointInvariantAliasBallotCertificates
   DEF PointLift!ElectionWinnerFacts, LiftedSafety!ElectionWinnerFacts

THEOREM PointInvariantAliasElectionInvariant ==
    PointLift!ElectionInvariant = LiftedSafety!ElectionInvariant
BY ONLY ZenonT(10), PointInvariantAliasElectionBallotFacts, PointInvariantAliasElectionInboxFacts, PointInvariantAliasElectionRequestFacts, PointInvariantAliasElectionTypes, PointInvariantAliasElectionWinnerFacts
   DEF PointLift!ElectionInvariant, LiftedSafety!ElectionInvariant

THEOREM PointInvariantAliasEntryBoundaryCounts ==
    PointLift!EntryBoundaryCounts = LiftedSafety!EntryBoundaryCounts
BY ONLY ZenonT(10), PointInvariantAliasCount
   DEF PointLift!EntryBoundaryCounts, LiftedSafety!EntryBoundaryCounts

THEOREM PointInvariantAliasEpochAckers ==
    \A t, e : PointLift!EpochAckers(t, e) = LiftedSafety!EpochAckers(t, e)
BY ONLY ZenonT(10)
   DEF PointLift!EpochAckers, LiftedSafety!EpochAckers

THEOREM PointInvariantAliasKnowledgeAt ==
    \A K, T, H : PointLift!KnowledgeAt(K, T, H) = LiftedSafety!KnowledgeAt(K, T, H)
BY ONLY ZenonT(10), PointInvariantAliasKnownBy
   DEF PointLift!KnowledgeAt, LiftedSafety!KnowledgeAt

THEOREM PointInvariantAliasNotificationsAt ==
    \A M, H : PointLift!NotificationsAt(M, H) = LiftedSafety!NotificationsAt(M, H)
BY ONLY ZenonT(10), PointInvariantAliasKnownBy
   DEF PointLift!NotificationsAt, LiftedSafety!NotificationsAt

THEOREM PointInvariantAliasEpochKnowledgeInvariant ==
    PointLift!EpochKnowledgeInvariant = LiftedSafety!EpochKnowledgeInvariant
BY ONLY ZenonT(10), PointInvariantAliasKnowledgeAt, PointInvariantAliasNotificationsAt
   DEF PointLift!EpochKnowledgeInvariant, LiftedSafety!EpochKnowledgeInvariant

THEOREM PointInvariantAliasFiniteChannels ==
    PointLift!FiniteChannels = LiftedSafety!FiniteChannels
BY ONLY ZenonT(10), PointInvariantAliasIsFiniteSet
   DEF PointLift!FiniteChannels, LiftedSafety!FiniteChannels

THEOREM PointInvariantAliasFiniteNodeData ==
    PointLift!FiniteNodeData = LiftedSafety!FiniteNodeData
BY ONLY ZenonT(10), PointInvariantAliasIsFiniteSet, PointInvariantAliasStorageShape
   DEF PointLift!FiniteNodeData, LiftedSafety!FiniteNodeData

THEOREM PointInvariantAliasFiniteProposals ==
    PointLift!FiniteProposals = LiftedSafety!FiniteProposals
BY ONLY ZenonT(10), PointInvariantAliasIsFiniteSet, PointInvariantAliasResult
   DEF PointLift!FiniteProposals, LiftedSafety!FiniteProposals

THEOREM PointInvariantAliasFiniteSnapshots ==
    PointLift!FiniteSnapshots = LiftedSafety!FiniteSnapshots
BY ONLY ZenonT(10), PointInvariantAliasIsFiniteSet
   DEF PointLift!FiniteSnapshots, LiftedSafety!FiniteSnapshots

THEOREM PointInvariantAliasFiniteLogInvariant ==
    PointLift!FiniteLogInvariant = LiftedSafety!FiniteLogInvariant
BY ONLY ZenonT(10), PointInvariantAliasFiniteChannels, PointInvariantAliasFiniteNodeData, PointInvariantAliasFiniteProposals, PointInvariantAliasFiniteSnapshots
   DEF PointLift!FiniteLogInvariant, LiftedSafety!FiniteLogInvariant

THEOREM PointInvariantAliasFollowerPrefixEvidence ==
    \A F, T, R, H : PointLift!FollowerPrefixEvidence(F, T, R, H) = LiftedSafety!FollowerPrefixEvidence(F, T, R, H)
BY ONLY ZenonT(10)
   DEF PointLift!FollowerPrefixEvidence, LiftedSafety!FollowerPrefixEvidence,
       PointLift!KnownBy, LiftedSafety!KnownBy, PointLift!Prefix, LiftedSafety!Prefix

THEOREM PointInvariantAliasFormalEntriesFrom ==
    \A F, V, P : PointLift!FormalEntriesFrom(F, V, P) = LiftedSafety!FormalEntriesFrom(F, V, P)
BY ONLY ZenonT(10), PointInvariantAliasCertifiedLogEntries
   DEF PointLift!FormalEntriesFrom, LiftedSafety!FormalEntriesFrom

=============================================================================
