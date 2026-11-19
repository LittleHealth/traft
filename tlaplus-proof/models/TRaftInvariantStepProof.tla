------------------------ MODULE TRaftInvariantStepProof ----------------------
EXTENDS TRaftAckSourceProof, TRaftCertifiedHistoryProof, TRaftPrefixEvidenceInduction, TRaftClosedHistoryProof, TRaftHistoryOriginProof, TRaftContextOriginProof, TRaftBoundaryInduction, TRaftLeaderHistoryProof, TRaftCanonicalDefinitionProof, TRaftInvariantDefinitions, TRaftElectionTemporal, TRaftControlTemporal,
        TRaftFiniteTemporal, TRaftDurabilityProof, TRaftCanonicalFiniteProof,
        TRaftHistoryFactsProof, TRaftOfferProof, TRaftCommitTemporal,
        TRaftRecoveryInduction, TRaftRecoveryOriginInduction, TRaftSafetyClosureInduction
USE FormalFaultsDisabled DEF FormalFaultsDisabled

THEOREM InductiveStep ==
    ASSUME Inv, ProofNext
    PROVE Inv'
<1>1. ElectionInvariant'
    BY ElectionInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>2. ControlInvariant'
    BY ControlInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>3. DurabilityInvariant'
    BY DurabilityInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>4. FiniteLogInvariant'
    BY FiniteLogInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>5. CanonicalFinite'
    BY CanonicalFiniteStep, <1>4 DEF Inv, ProofInvariant, ProofNext
<1>6. CanonicalViewLinks'
    BY CanonicalViewLinksStep, <1>1 DEF Inv, ProofInvariant, ProofNext, Next
<1>7. OfferProvenance'
    BY OfferInductiveStep DEF Inv, ProofInvariant, ProofNext
<1>8. KnowledgeInvariant'
    BY KnowledgeInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant,
       ProofNext, CommitFaultsDisabled
<1>9. RecoveryInvariant'
    BY RecoveryInvariantInductiveStep
<1>10. RecoveryOriginFacts'
    BY RecoveryOriginInductiveStep, <1>9, <1>4, <1>2
<1>101. EntryBoundaryCounts'
    BY EntryBoundaryInductiveStep
<1>102. LeaderHistoryInvariant'
    BY LeaderHistoryInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>103. CanonicalDefinition'
    BY CanonicalDefinitionStep DEF Inv, ProofInvariant
<1>104. HistoryOriginInvariant'
    <2>1. applied \in [Replicas -> SUBSET Entries]
        BY DEF Inv, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. AppliedShape
        BY ONLY SMT, <2>1 DEF AppliedShape
    <2>3. HistoryOriginInvariant /\ CommittedKnowledgeSound /\ Next
        BY DEF Inv, ProofInvariant, Safety, ProofNext
    <2> QED BY HistoryOriginsInductiveStep, <2>2, <2>3
<1>105. ContextOrigins(canonical', entryContexts')
    BY ContextOriginsInductiveStep, <1>9
       DEF Inv, ProofInvariant, ProofNext, Next, RecoveryInvariant
<1>106. HistoryPartitionCompleteness'
    BY ClosedHistoriesInductiveStep, <1>9, <1>4
       DEF Inv, ProofInvariant, ProofNext, Next
<1>107. PrefixEvidenceInvariant'
    BY PrefixEvidenceInductiveStep, <1>9
<1>108. InstalledEntriesHaveSource'
    BY InstalledSourceInductiveStep
       DEF Inv, ProofInvariant, PreProvenanceInvariant, DurabilityInvariant, DurableData, ProofNext
<1>109. CertifiedPartitionHistory'
    BY CertifiedHistoriesInductiveStep, <1>9, <1>4, <1>108
       DEF Inv, ProofInvariant, ProofNext
<1>110. MessageSourceInvariant'
    BY MessageSourcesInductiveStep DEF Inv, ProofInvariant, PreProvenanceInvariant,
       DurabilityInvariant, DurableData, ProofNext, Next
<1>11. ProofInvariant'
    BY <1>110, <1>108, <1>109, <1>107, <1>106, <1>104, <1>105, <1>101, <1>102, <1>103, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10
       DEF ProofInvariant, PreProvenanceInvariant
<1>12. Safety'
    BY SafetyClosureInductiveStep, <1>11
<1> QED BY <1>11, <1>12 DEF Inv
=============================================================================
