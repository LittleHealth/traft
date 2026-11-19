------------------- MODULE TRaftLiftedProtocolDefinitions -------------------
EXTENDS TRaftInvariantDefinitions, TRaftHistoryRefinementProof

\* The history substitution is observational. Its complete proof closure is
\* checked independently by the acceptance tool. No protocol guard is added.
LiftedSafety == INSTANCE TRaftSafetyObligations WITH canonical <- DerivedCanonical
=============================================================================
