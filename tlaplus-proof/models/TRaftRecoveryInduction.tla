------------------------ MODULE TRaftRecoveryInduction -----------------------
EXTENDS TRaftInvariantDefinitions, TRaftTermAndVoteProof, TRaftReportFenceProof, TRaftPotentialPreservationProof, TRaftAckOriginProof, TRaftPotentialCoverageProof, TRaftTypeProof, TRaftCanonicalShapeInduction
USE FormalFaultsDisabled, ParameterAssumptions, SentinelSeparation
    DEF FormalFaultsDisabled, ParameterAssumptions, SentinelSeparation

\* Separate preservation obligations; any failed leaf blocks full Safety.
THEOREM RecoveryInvariantInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE RecoveryInvariant'
<1>1. ElectionInvariant' /\ ControlInvariant'
    BY ElectionInductiveStep, ControlInductiveStep
       DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext
<1>2. StrongLayersImplyTermAndVoteFacts'
    BY ONLY PTL, StrongLayersImplyTermAndVoteFacts
<1>3. TermAndVoteFacts'
    BY ONLY <1>1, <1>2
<1>4. TypeOK'
    BY TypeOKInductiveStep
<1>5. CanonicalShape'
    BY CanonicalShapeInductiveStep, <1>4
<1>6. AckOrigin'
    BY AckOriginInductiveStep
<1>7. ReportFences'
    BY ReportFencesInductiveStep
<1>8. PotentialCoverage'
    BY PotentialCoverageInductiveStep
<1>9. PotentialPreservation'
    BY PotentialPreservationInductiveStep, <1>1, <1>4, <1>5 DEF Inv, TypeOK
<1> QED BY ONLY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF RecoveryInvariant
=============================================================================
