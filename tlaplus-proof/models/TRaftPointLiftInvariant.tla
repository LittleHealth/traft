---------------------- MODULE TRaftPointLiftInvariant ----------------------
EXTENDS TRaftPointLiftInterface, TRaftPointInvariantAliases04

THEOREM PointLiftStateIdentities ==
    /\ (PointLift!ProofInvariant <=> LiftedSafety!ProofInvariant)
    /\ (PointLift!CanonicalShape <=> LiftedSafety!CanonicalShape)
BY ONLY SMT, PointInvariantAliasProofInvariant, PointInvariantAliasCanonicalShape
=============================================================================
