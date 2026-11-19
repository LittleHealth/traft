---------------------- MODULE TRaftPrefixEvidenceInduction -------------------
EXTENDS TRaftPrefixFollowerInduction, TRaftPrefixOfferInduction, TRaftPrefixAckInduction,
        TRaftInvariantDefinitions, TRaftEpochKnowledgeProof,
        TRaftActivationCertificateProof, TRaftRecoveryEpochProof
USE FormalFaultsDisabled DEF FormalFaultsDisabled

\* The three prefix-source preservation goals remain explicit obligations.
\* They are not assumptions of Spec and must not be accepted on root success.
THEOREM PrefixEvidenceInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant'
    PROVE PrefixEvidenceInvariant'
<1>1. EpochKnowledgeInvariant'
    BY EpochKnowledgeInductiveStep DEF Inv, ProofInvariant, PrefixEvidenceInvariant,
       PreProvenanceInvariant, ProofNext, CommitFaultsDisabled
<1>2. ActiveRecoveryCertificates'
    BY ActiveRecoveryCertificatesStep DEF Inv, ProofInvariant, PrefixEvidenceInvariant,
       PreProvenanceInvariant, ProofNext
<1>3. RecoveryProposalBoundaries(proposals')
    BY RecoveryProposalBoundariesInductiveStep DEF Inv, Safety, ProofInvariant,
       PrefixEvidenceInvariant, ProofNext, Next
<1>4. FollowerPrefixEvidence(formal', term', retained', commitHistory')
    BY FollowerPrefixEvidenceInductiveStep
<1>5. OfferCountEvidence(offers', entryContexts', commitHistory')
    BY OfferPrefixEvidenceInductiveStep
<1>6. AckPrefixEvidence(ackMessages', entryContexts', commitHistory')
    BY AckPrefixEvidenceInductiveStep
<1> QED BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF PrefixEvidenceInvariant
=============================================================================
