------------------------- MODULE TRaftSafetyEntryContexts --------------------
EXTENDS TRaftEntryContextProof, TRaftDurabilityProof

THEOREM EntryContextUniqueInductiveStep ==
    ASSUME Inv, ProofNext, ProofInvariant'
    PROVE EntryContextUnique'
<1>1. RecoveryInvariant'
    BY DEF ProofInvariant, PreProvenanceInvariant
<1>2. CommitEvidenceSound'
    BY EvidenceInductiveStep DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, ProofNext
<1> QED BY ExactEntryContextsInductiveStep, <1>1, <1>2
=============================================================================
