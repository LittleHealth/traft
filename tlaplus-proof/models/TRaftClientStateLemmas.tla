------------------------ MODULE TRaftClientStateLemmas -----------------------
EXTENDS TRaftClientRequestSources, TRaftApplicationPrefixProof,
        TRaftReadResultAgreement, TRaftClientReturnedWitness,
        TRaftEvidenceLinearizationOrder

\* Collect the existing generic proof families without importing
\* TRaftProtocolSafety or the client temporal composition modules.
\* One canonical-history substitution shares their original definitions;
\* every imported theorem still needs its separate frozen-source check.
=============================================================================
