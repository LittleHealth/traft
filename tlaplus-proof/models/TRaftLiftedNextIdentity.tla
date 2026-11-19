---------------------- MODULE TRaftLiftedNextIdentity ----------------------
EXTENDS TRaftLiftedInitialIdentity

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM LiftedSafetyNextIdentity ==
    LiftedSafety!ProofNext <=> LiftedNext(DerivedCanonical)
BY ONLY ZenonT(10), LiftedCoreAliasNext, LiftedCoreAliasTerms
   DEF LiftedSafety!ProofNext, LiftedSafety!GhostNext, LiftedNext, ProposedAt,
       Result, LiftedSafety!Result
=============================================================================
