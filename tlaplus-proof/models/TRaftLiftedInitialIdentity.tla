---------------------- MODULE TRaftLiftedInitialIdentity ----------------------
EXTENDS TRaftLiftedSafetyParameters

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedSafetyInitIdentity ==
    LiftedSafety!ProofInit <=> LiftedInit(DerivedCanonical)
BY ONLY ZenonT(10), LiftedCoreAliasInit, LiftedCoreAliasTerms
   DEF LiftedSafety!ProofInit, LiftedSafety!GhostInit, LiftedInit

THEOREM LiftedSafetyVarsIdentity ==
    LiftedSafety!proofVars = <<vars, DerivedCanonical>>
BY ONLY ZenonT(10), LiftedCoreAliasvars DEF LiftedSafety!proofVars
=============================================================================
