---------------------- MODULE TRaftPointLiftDefinitions ----------------------
EXTENDS TRaftClientRequestSources, TRaftClientRefinementProof,
        TRaftInvariantDefinitions

\* Proof-only instance sharing and transport; no protocol guard or premise.

\* Share the same history substitution for partition, source, prefix, read,
\* witness and evidence-order state lemmas. Each dependency is still checked.
\* The unqualified proof families are imported only by their actual callers;
\* avoid loading a second copy of every client lemma in each identity module.
PointLift == INSTANCE TRaftClientStateLemmas WITH canonical <- DerivedCanonical
DerivedPointLogs == CanonicalPointLogs(DerivedCanonical)
=============================================================================
