------------------------- MODULE TRaftDiagnosticProof ------------------------
EXTENDS TRaftInductionDiagnostic, TRaftElectionTemporal

THEOREM StrengtheningRejectsOldCountermodel ==
    DiagnosticInit => ~ProofInvariant
BY SMT DEF DiagnosticInit, BadRequest, ProofInvariant, PreProvenanceInvariant,
           ElectionInvariant, ElectionRequestFacts

THEOREM RequestConditionIsProtocolInvariant ==
    Spec => []ElectionRequestFacts
BY PTL, ElectionInvariantAlways DEF ElectionInvariant

\* The exclusion is justified by a proved invariant of the original protocol.
\* Neither DiagnosticInit nor ProofInvariant is a guard of ProtocolNext.
=============================================================================
