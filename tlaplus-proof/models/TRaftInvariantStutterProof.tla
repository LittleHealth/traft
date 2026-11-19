----------------------- MODULE TRaftInvariantStutterProof --------------------
EXTENDS TRaftInvariantDefinitions, TLAPS

THEOREM StutteringPreservesInvariant ==
    ASSUME Inv, UNCHANGED proofVars
    PROVE Inv'
<1>1. TypeOK'
    <2>1. TypeOK
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF TypeOK, observerVars, proofVars, protocolVars, vars
<1>2. ElectionSafety'
    <2>1. ElectionSafety
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF ElectionSafety, observerVars, proofVars, protocolVars, vars
<1>3. LeaderAppendOnly'
    <2>1. LeaderAppendOnly
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF LeaderAppendOnly, observerVars, proofVars, protocolVars, vars
<1>4. LogMatching'
    <2>1. LogMatching
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF LogMatching, observerVars, proofVars, protocolVars, vars
<1>5. CommittedPartitionAgreement'
    <2>1. CommittedPartitionAgreement
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CommittedPartitionAgreement, observerVars, proofVars, protocolVars, vars
<1>6. IntraPartitionRankEquivalence'
    <2>1. IntraPartitionRankEquivalence
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF IntraPartitionRankEquivalence, observerVars, proofVars, protocolVars, vars
<1>7. PartitionLeaderCompleteness'
    <2>1. PartitionLeaderCompleteness
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF PartitionLeaderCompleteness, observerVars, proofVars, protocolVars, vars
<1>8. EntryLeaderCompleteness'
    <2>1. EntryLeaderCompleteness
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF EntryLeaderCompleteness, observerVars, proofVars, protocolVars, vars
<1>9. StateMachineSafety'
    <2>1. StateMachineSafety
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF StateMachineSafety, observerVars, proofVars, protocolVars, vars
<1>10. PartitionStateMachineSafety'
    <2>1. PartitionStateMachineSafety
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF PartitionStateMachineSafety, observerVars, proofVars, protocolVars, vars
<1>11. ApplicationOrder'
    <2>1. ApplicationOrder
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF ApplicationOrder, observerVars, proofVars, protocolVars, vars
<1>12. CommittedKnowledgeSound'
    <2>1. CommittedKnowledgeSound
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CommittedKnowledgeSound, observerVars, proofVars, protocolVars, vars
<1>13. AppliedEntriesPreserved'
    <2>1. AppliedEntriesPreserved
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF AppliedEntriesPreserved, observerVars, proofVars, protocolVars, vars
<1>14. RecoveryUnionCoherent'
    <2>1. RecoveryUnionCoherent
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED <<role, phase, reports, term>>
        BY SMT DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF Recovered, RecoveryUnionCoherent, ReportedEntries, ReportedProposals, Reporters, observerVars, proofVars, protocolVars, vars
<1>15. RecoveryCandidatesPreserveEvidence'
    <2>1. RecoveryCandidatesPreserveEvidence
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED <<role, phase, reports, term, commitHistory>>
        BY SMT DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF Recovered, RecoveryCandidatesPreserveEvidence, ReportedEntries, ReportedProposals, Reporters, observerVars, proofVars, protocolVars, vars
<1>16. RecoveryReportsHaveOrigin'
    <2>1. RecoveryReportsHaveOrigin
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. role' = role /\ phase' = phase /\ reports' = reports /\ term' = term
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF RecoveryReportsHaveOrigin, ReportedEntries, ReportedProposals, Reporters, observerVars, proofVars, protocolVars, vars
<1>17. QuorumProposalPreservation'
    <2>1. QuorumProposalPreservation
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. proposals' = proposals /\ ackMessages' = ackMessages /\ leaderViews' = leaderViews
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF Ack, QuorumProposalPreservation, observerVars, proofVars, protocolVars, vars
<1>18. RecoveryPreservesCommitted'
    <2>1. RecoveryPreservesCommitted
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF RecoveryPreservesCommitted, observerVars, proofVars, protocolVars, vars
<1>19. CommitEvidenceSound'
    <2>1. CommitEvidenceSound
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CommitEvidenceSound, observerVars, proofVars, protocolVars, vars
<1>20. CommitEvidenceAgreement'
    <2>1. CommitEvidenceAgreement
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CommitEvidenceAgreement, observerVars, proofVars, protocolVars, vars
<1>21. CommitNoticeHasQuorum'
    <2>1. CommitNoticeHasQuorum
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CommitNoticeHasQuorum, observerVars, proofVars, protocolVars, vars
<1>22. ConfirmationHasQuorum'
    <2>1. ConfirmationHasQuorum
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. confirmations' = confirmations /\ ackMessages' = ackMessages
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF Ack, ConfirmationHasQuorum, observerVars, proofVars, protocolVars, vars
<1>23. AckDurability'
    <2>1. AckDurability
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF AckDurability, observerVars, proofVars, protocolVars, vars
<1>24. EvidenceRespectsPartitionOrder'
    <2>1. EvidenceRespectsPartitionOrder
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF EvidenceRespectsPartitionOrder, observerVars, proofVars, protocolVars, vars
<1>25. NormalCountCheckSound'
    <2>1. NormalCountCheckSound
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF Aligned, CanReceive, NormalCountCheckSound, observerVars, proofVars, protocolVars, vars
<1>26. EntryContextUnique'
    <2>1. EntryContextUnique
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF EntryContextUnique, observerVars, proofVars, protocolVars, vars
<1>27. TermAndVoteFacts'
    <2>1. TermAndVoteFacts
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF TermAndVoteFacts, observerVars, proofVars, protocolVars, vars
<1>28. CanonicalShape'
    <2>1. CanonicalShape
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. canonical' = canonical /\ proposals' = proposals /\ formal' = formal /\ entryContexts' = entryContexts /\ term' = term /\ role' = role /\ reportMessages' = reportMessages
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF CanonicalShape, Sublog, ContextSound, observerVars, proofVars, protocolVars, vars
<1>29. AckOrigin'
    <2>1. AckOrigin
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF AckOrigin, observerVars, proofVars, protocolVars, vars
<1>30. ReportFences'
    <2>1. ReportFences
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. retained' = retained /\ term' = term /\ reports' = reports /\ reportMessages' = reportMessages /\ proposals' = proposals
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF ReportFences, Reporters, observerVars, proofVars, protocolVars, vars
<1>31. PotentialCoverage'
    <2>1. PotentialCoverage
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. ackMessages' = ackMessages /\ term' = term /\ formal' = formal /\ retained' = retained /\ reportMessages' = reportMessages
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF MayChoose, PossibleAckers, EpochAckers, PotentialCoverage, RetainedContents, observerVars, proofVars, protocolVars, vars
<1>32. PotentialPreservation'
    <2>1. PotentialPreservation
        BY DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>2. proposals' = proposals /\ leaderViews' = leaderViews /\ ackMessages' = ackMessages /\ term' = term
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF IssuedEntries, MayChoose, PossibleAckers, EpochAckers, PotentialPreservation, observerVars, proofVars, protocolVars, vars
<1>33. ElectionInvariant'
    <2>1. ElectionInvariant
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. term' = term /\ vote' = vote /\ role' = role /\ voteInbox' = voteInbox /\ voteRequests' = voteRequests /\ voteMessages' = voteMessages /\ winners' = winners
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF ElectionCoreVars, ElectionVars, BallotVoters, BallotCertificates, ElectionTypes, ElectionRequestFacts, ElectionBallotFacts, ElectionInboxFacts, ElectionWinnerFacts, ElectionInvariant, ObserveWinners, ElectionChangingNext, proofVars, vars, protocolVars, observerVars
<1>34. ControlInvariant'
    <2>1. ControlInvariant
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF Reporters, ControlCoreVars, ControlVars, ControlShape, OwnedEpochs, ProposalProvenance, UnusedProposalEpoch, RecoveryRequestProvenance, ReportProvenance, CollectedReportProvenance, ControlInvariant, ControlChangingNext, UniqueProposalEpoch, proofVars, vars, protocolVars, observerVars
<1>35. DurabilityInvariant'
    <2>1. DurabilityInvariant
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF AckDurability, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, DurableData, AckSendersValid, DurabilityInvariant, DurabilityStep, proofVars, vars, protocolVars, observerVars
<1>36. FiniteLogInvariant'
    <2>1. FiniteLogInvariant
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF FiniteChannelVars, FiniteNodeVars, FiniteSnapshotVars, FiniteChannels, FiniteNodeData, FiniteProposals, FiniteSnapshots, FiniteLogInvariant, FiniteLogVars, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, DurableData, AckSendersValid, DurabilityInvariant, DurabilityStep, proofVars, vars, protocolVars, observerVars
<1>37. RecoveryOriginFacts'
    <2>1. RecoveryOriginFacts /\ UNCHANGED proofVars
        BY SMT DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2> QED BY ONLY SMT, <2>1 DEF RecoveryOriginFacts, proofVars, vars, protocolVars, observerVars
<1>38. CanonicalFinite'
    BY SMT DEF Inv, ProofInvariant, CanonicalFinite, proofVars
<1>39. CanonicalViewLinks'
    <2>1. CanonicalViewLinks
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF CanonicalViewLinks, proofVars, vars, protocolVars, observerVars
<1>40. OfferProvenance'
    <2>1. OfferProvenance
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. UNCHANGED proofVars
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF OfferProvenance, OfferVars, proofVars, vars, protocolVars, observerVars
<1>41. KnowledgeInvariant'
    <2>1. KnowledgeInvariant
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant
    <2>2. ackInbox' = ackInbox /\ ackMessages' = ackMessages /\ knownCommitted' = knownCommitted /\ commitMessages' = commitMessages /\ commitHistory' = commitHistory /\ confirmations' = confirmations
        BY DEF proofVars, vars, protocolVars, observerVars
    <2> QED BY ONLY IsaM("auto"), <2>1, <2>2 DEF AckInboxOrigins, CommitMessageEvidence, KnowledgeShape, KnowledgeInvariant, KnowledgeVars, CommitFaultsDisabled, ProposalSenders, CommittedKnowledgeSound, ConfirmationHasQuorum, Ack, proofVars, vars, protocolVars, observerVars
<1>43. EntryBoundaryCounts'
    <2>1. EntryBoundaryCounts
        BY DEF Inv, ProofInvariant
    <2>2. UNCHANGED entryContexts
        BY DEF proofVars, vars, observerVars
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF EntryBoundaryCounts
<1>44. LeaderHistoryInvariant'
    BY SMT DEF Inv, ProofInvariant, proofVars, vars, protocolVars, observerVars, LeaderHistoryInvariant, PastLeaderViews, LeaderViewCertificates
<1>45. CanonicalDefinition'
    BY SMT DEF Inv, ProofInvariant, proofVars, vars, protocolVars, observerVars, CanonicalDefinition, DerivedCanonical, ProposedAt, ViewedAt
<1>46. HistoryOriginInvariant'
    <2>1. HistoryOriginInvariant /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF HistoryOriginInvariant, AppliedEvidence,
        AppliedPartitionOrigins, PartitionHistoryOrigins, proofVars, vars, protocolVars, observerVars
<1>47. ContextOrigins(canonical', entryContexts')
    <2>1. ContextOrigins(canonical, entryContexts) /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF ContextOrigins, proofVars, vars, protocolVars, observerVars
<1>48. HistoryPartitionCompleteness'
    <2>1. HistoryPartitionCompleteness /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF HistoryPartitionCompleteness,
        ClosedPartitionOrigins, HasClosedContext, proofVars, vars, protocolVars, observerVars
<1>49. PrefixEvidenceInvariant'
    <2>1. PrefixEvidenceInvariant /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF PrefixEvidenceInvariant, EpochKnowledgeInvariant,
       KnowledgeAt, NotificationsAt, FollowerPrefixEvidence, OfferCountEvidence,
       AckPrefixEvidence, RecoveryProposalBoundaries, ActiveRecoveryCertificates, ActiveControlCertified, LeaderViewsCertified,
       proofVars, vars, protocolVars, observerVars
<1>50. InstalledEntriesHaveSource'
    <2>1. InstalledEntriesHaveSource /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF InstalledEntriesHaveSource, FormalEntriesFrom,
        CertifiedLogEntries, proofVars, vars, protocolVars, observerVars
<1>51. CertifiedPartitionHistory'
    <2>1. CertifiedPartitionHistory /\ UNCHANGED proofVars
        BY DEF Inv, ProofInvariant
    <2> QED BY ONLY SMT, <2>1 DEF CertifiedPartitionHistory, CertifiedContexts,
        CertifiedLogEntries, ClosedPartitionOrigins, HasClosedContext, proofVars, vars, protocolVars, observerVars
<1>52. MessageSourceInvariant'
    <2>1. MessageSourceInvariant
        BY DEF Inv, ProofInvariant
    <2>2. UNCHANGED <<ackMessages, proposals, offers, retained, confirmations>>
        BY DEF proofVars, vars, protocolVars
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF MessageSourceInvariant, AckSourceInvariant,
        RetainedProposalsActual, ConfirmationSources
<1> QED BY <1>52, <1>50, <1>51, <1>49, <1>48, <1>46, <1>47, <1>44, <1>45, <1>43, SMT, <1>38, <1>39, <1>40, <1>41, <1>34, <1>35, <1>36, <1>37, <1>33, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26, <1>27, <1>28, <1>29, <1>30, <1>31, <1>32 DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant

=============================================================================
