---------------------- MODULE TRaftLiftedSafetyTransport ----------------------
EXTENDS TRaftLiftedInvariantTransport

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedSafetyWithoutFreeHistory ==
    LiftedSpec(DerivedCanonical) => []Safety
BY ONLY PTL, LiftedSafety!ObservedProtocolSafety,
        LiftedSafetyParameters, LiftedSafetySpecificationIdentity, LiftedSafetyPredicateIdentity
   DEF LiftedSafety!ParameterAssumptions, LiftedSafety!SentinelSeparation,
       LiftedSafety!FormalFaultsDisabled, LiftedSafety!CommitProofFaultsDisabled,
       LiftedSafety!CommitFaultsDisabled
=============================================================================
