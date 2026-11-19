---------------------------- MODULE TRaftInitProof ---------------------------
EXTENDS TRaftOfferProof, TRaftCommitSupport, TRaftProofState, TRaftElectionSupport, TRaftControlSupport, TRaftDurabilityProof,
        TRaftFiniteSupport, FiniteSetTheorems, TLAPS
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation
THEOREM InitEstablishesInvariant ==
    ASSUME ProofInit
    PROVE Safety /\ ProofInvariant
<1>1. TypeOK
    BY SMT, FS_EmptySet DEF Coherent, Count, Cur, EmptyReports, Entries, GhostInit, Indices, Init, LastIndex, MaxOr, NoNode, NoProposal, NoReport, Part, Partitions, Phases, ProofInit, ProposalRecords, Result, Roles, Terms, TypeOK
<1>2. ElectionSafety
    BY SMT, FS_EmptySet DEF ElectionSafety, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>3. LeaderAppendOnly
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, LeaderAppendOnly, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>4. LogMatching
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Indices, Init, LogMatching, NoNode, NoProposal, NoReport, Origin, Part, Partitions, Prefix, ProofInit, Terms
<1>5. CommittedPartitionAgreement
    BY SMT, FS_EmptySet DEF CommittedPartitionAgreement, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>6. IntraPartitionRankEquivalence
    BY SMT, FS_EmptySet DEF ClosedPrefix, Count, Cur, EmptyReports, GhostInit, Init, IntraPartitionRankEquivalence, LastIndex, LastTerm, MaxOr, NoNode, NoProposal, NoReport, Origin, Part, Prefix, ProofInit, Rank, Terms
<1>7. PartitionLeaderCompleteness
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, Part, PartitionLeaderCompleteness, ProofInit, Terms
<1>8. EntryLeaderCompleteness
    BY SMT, FS_EmptySet DEF EmptyReports, EntryLeaderCompleteness, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>9. StateMachineSafety
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, StateMachineSafety, Terms
<1>10. PartitionStateMachineSafety
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, PartitionStateMachineSafety, ProofInit, Terms
<1>11. ApplicationOrder
    BY SMT, FS_EmptySet DEF ApplicationOrder, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>12. CommittedKnowledgeSound
    BY SMT, FS_EmptySet DEF CommittedKnowledgeSound, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>13. AppliedEntriesPreserved
    BY SMT, FS_EmptySet DEF AppliedEntriesPreserved, BuildRecovery, Count, Cur, EmptyReports, Entry, GhostInit, Indices, Init, LastIndex, Later, Latest, MaxOr, NoNode, NoProposal, NoReport, Part, Partitions, ProofInit, Proposal, Quorum, Recovered, ReportedEntries, ReportedProposals, Reporters, Result, Terms
<1>14. RecoveryUnionCoherent
    BY SMT, FS_EmptySet DEF Coherent, EmptyReports, GhostInit, Init, Later, Latest, NoNode, NoProposal, NoReport, ProofInit, Quorum, Recovered, RecoveryUnionCoherent, ReportedEntries, ReportedProposals, Reporters, Result, Terms
<1>15. RecoveryCandidatesPreserveEvidence
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, Later, Latest, NoNode, NoProposal, NoReport, ProofInit, Quorum, Recovered, RecoveryCandidatesPreserveEvidence, ReportedEntries, ReportedProposals, Reporters, Result, Terms
<1>16. RecoveryReportsHaveOrigin
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Quorum, RecoveryReportsHaveOrigin, ReportedEntries, ReportedProposals, Reporters, Result, Terms
<1>17. QuorumProposalPreservation
    BY SMT, FS_EmptySet DEF Ack, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Quorum, QuorumProposalPreservation, Result, Terms
<1>18. RecoveryPreservesCommitted
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, RecoveryPreservesCommitted, Terms
<1>19. CommitEvidenceSound
    BY SMT, FS_EmptySet DEF CommitEvidenceSound, EmptyReports, Evidence, GhostInit, Init, MessageAckers, NoNode, NoProposal, NoReport, ProofInit, Quorum, Terms
<1>20. CommitEvidenceAgreement
    BY SMT, FS_EmptySet DEF CommitEvidenceAgreement, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>21. CommitNoticeHasQuorum
    BY SMT, FS_EmptySet DEF CommitNoticeHasQuorum, EmptyReports, GhostInit, Init, MessageAckers, NoNode, NoProposal, NoReport, ProofInit, Quorum, Terms
<1>22. ConfirmationHasQuorum
    BY SMT, FS_EmptySet DEF Ack, ConfirmationHasQuorum, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Quorum, Result, Terms
<1>23. AckDurability
    BY SMT, FS_EmptySet DEF AckDurability, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>24. EvidenceRespectsPartitionOrder
    BY SMT, FS_EmptySet DEF EmptyReports, EvidenceRespectsPartitionOrder, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>25. NormalCountCheckSound
    BY SMT, FS_EmptySet DEF Aligned, CanReceive, Count, Cur, EmptyReports, GhostInit, Init, MaxOr, NoNode, NoProposal, NoReport, NormalCountCheckSound, Origin, Part, Prefix, ProofInit, Terms
<1>26. EntryContextUnique
    BY SMT, FS_EmptySet DEF EmptyReports, EntryContextUnique, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Terms
<1>27. TermAndVoteFacts
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Quorum, TermAndVoteFacts, Terms
<1>28. CanonicalShape
    <2>1. canonical = [t \in Terms |-> {}] /\ proposals = {} /\ reportMessages = {}
          /\ formal = [r \in Replicas |-> {}] /\ role = [r \in Replicas |-> "Follower"]
        BY SMT DEF ProofInit, Init, GhostInit
    <2>2. 0 <= MaxPartitionSize
        BY SMT DEF ParameterAssumptions
    <2>3. \A t \in Terms : \A q \in Partitions : Count(canonical[t], q) <= MaxPartitionSize
        BY SMT, <2>1, <2>2, FS_EmptySet DEF Count, Part
    <2>4. canonical \in [Terms -> SUBSET Entries]
          /\ \A t \in Terms : Coherent(canonical[t]) /\ ContextSound(canonical[t])
                 /\ \A e \in canonical[t] : e.term <= t
        BY SMT, <2>1 DEF Coherent, ContextSound
    <2>5. \A r \in Replicas : Sublog(formal[r]) /\ ContextSound(formal[r])
                 /\ (\A e \in formal[r] : e.term <= term[r])
                 /\ (role[r] = "Leader" => formal[r] = canonical[term[r]])
        BY SMT, <2>1 DEF Sublog, ContextSound
    <2> QED BY SMT, <2>1, <2>3, <2>4, <2>5 DEF CanonicalShape
<1>29. AckOrigin
    BY SMT, FS_EmptySet DEF AckOrigin, EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Result, Terms
<1>30. ReportFences
    BY SMT, FS_EmptySet DEF EmptyReports, GhostInit, Init, NoNode, NoProposal, NoReport, ProofInit, Quorum, ReportFences, Reporters, Terms
<1>31. PotentialCoverage
    BY SMT, FS_EmptySet DEF EmptyReports, EpochAckers, GhostInit, Init, MayChoose, NoNode, NoProposal, NoReport, PossibleAckers, PotentialCoverage, ProofInit, Quorum, ReportContents, Result, RetainedContents, Terms
<1>32. PotentialPreservation
    BY SMT, FS_EmptySet DEF EmptyReports, EpochAckers, GhostInit, Init, IssuedEntries, MayChoose, NoNode, NoProposal, NoReport, PossibleAckers, PotentialPreservation, ProofInit, Quorum, Terms
<1>33. ElectionInvariant
    BY ElectionInvariantInitially DEF ProofInit
<1>34. ControlInvariant
    BY ControlInvariantInitially DEF ProofInit
<1>35. DurabilityInvariant
    BY DurabilityInitially DEF ProofInit
<1>36. FiniteLogInvariant
    BY FiniteLogInitially DEF ProofInit
<1>37. RecoveryOriginFacts
    BY SMT DEF RecoveryOriginFacts, ProofInit, Init, GhostInit
<1>38. CanonicalFinite
    BY SMT, FS_EmptySet DEF ProofInit, GhostInit, CanonicalFinite
<1>39. CanonicalViewLinks
    BY SMT DEF ProofInit, Init, CanonicalViewLinks
<1>40. OfferProvenance
    BY OfferProvenanceInitially DEF ProofInit
<1>41. KnowledgeInvariant
    BY KnowledgeInitially DEF ProofInit
<1>42. EntryBoundaryCounts
    BY SMT DEF EntryBoundaryCounts, ProofInit, Init
<1>43. LeaderHistoryInvariant
    BY SMT DEF ProofInit, Init, LeaderHistoryInvariant, PastLeaderViews, LeaderViewCertificates
<1>44. CanonicalDefinition
    <2>1. canonical = [t \in Terms |-> {}] /\ proposals = {} /\ leaderViews = {}
        BY DEF ProofInit, Init, GhostInit
    <2>2. \A t \in Terms : ProposedAt(proposals, t) = {} /\ ViewedAt(leaderViews, t) = {}
        BY ONLY SMT, <2>1 DEF ProposedAt, ViewedAt
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF CanonicalDefinition, DerivedCanonical
<1>45. HistoryOriginInvariant
    BY SMT DEF ProofInit, Init, HistoryOriginInvariant, AppliedEvidence,
       AppliedPartitionOrigins, PartitionHistoryOrigins
<1>46. ContextOrigins(canonical, entryContexts)
    BY SMT DEF ProofInit, Init, ContextOrigins
<1>47. HistoryPartitionCompleteness
    BY SMT DEF ProofInit, Init, HistoryPartitionCompleteness, ClosedPartitionOrigins
<1>48. PrefixEvidenceInvariant
    BY SMT DEF ProofInit, Init, PrefixEvidenceInvariant, EpochKnowledgeInvariant,
       KnowledgeAt, NotificationsAt, FollowerPrefixEvidence, OfferCountEvidence,
       AckPrefixEvidence, RecoveryProposalBoundaries, ActiveRecoveryCertificates, ActiveControlCertified, LeaderViewsCertified
<1>49. InstalledEntriesHaveSource
    BY SMT DEF ProofInit, Init, InstalledEntriesHaveSource, FormalEntriesFrom
<1>50. CertifiedPartitionHistory
    BY SMT DEF ProofInit, Init, CertifiedPartitionHistory, ClosedPartitionOrigins
<1>51. MessageSourceInvariant
    BY SMT DEF ProofInit, Init, MessageSourceInvariant, AckSourceInvariant,
       RetainedProposalsActual, ConfirmationSources
<1> QED BY SMT, <1>51, <1>49, <1>50, <1>48, <1>47, <1>45, <1>46, <1>43, <1>44, <1>42, <1>38, <1>39, <1>40, <1>41, <1>34, <1>35, <1>36, <1>37, <1>33, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26, <1>27, <1>28, <1>29, <1>30, <1>31, <1>32 DEF Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
=============================================================================
