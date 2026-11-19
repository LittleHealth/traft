---------------------- MODULE TRaftLiftedSpecificationIdentity ----------------------
EXTENDS TRaftLiftedNextIdentity

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedSafetySpecificationIdentity ==
    LiftedSafety!ProofSpec <=> LiftedSpec(DerivedCanonical)
<1>1. (LiftedSafety!proofVars = <<vars, DerivedCanonical>>)'
    BY ONLY PTL, LiftedSafetyVarsIdentity
<1>2. [LiftedSafety!ProofNext]_LiftedSafety!proofVars
          <=> [LiftedNext(DerivedCanonical)]_<<vars, DerivedCanonical>>
    BY ONLY SMT, LiftedSafetyNextIdentity, LiftedSafetyVarsIdentity, <1>1
<1> QED BY ONLY PTL, LiftedSafetyInitIdentity, <1>2
   DEF LiftedSafety!ProofSpec, LiftedSpec
=============================================================================
