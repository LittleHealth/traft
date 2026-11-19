---------------------- MODULE TRaftLiftedInvariantTransport ----------------------
EXTENDS TRaftLiftedSpecificationIdentity

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedInvariantWithoutFreeHistory ==
    LiftedSpec(DerivedCanonical) => []LiftedSafety!Inv
BY ONLY PTL, LiftedSafety!ObservedProtocolInvariant,
        LiftedSafetyParameters, LiftedSafetySpecificationIdentity
   DEF LiftedSafety!ParameterAssumptions, LiftedSafety!SentinelSeparation,
       LiftedSafety!FormalFaultsDisabled, LiftedSafety!CommitProofFaultsDisabled,
       LiftedSafety!CommitFaultsDisabled
=============================================================================
