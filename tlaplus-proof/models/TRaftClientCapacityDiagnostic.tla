-------------------- MODULE TRaftClientCapacityDiagnostic --------------------
EXTENDS TRaftApplicationScenarios

\* The existing reachable scenario has finished recovery and invoked PutX
\* at pc = 31. This observation does not restrict any transition.
FirstWriteEnabled == pc = 31 => ENABLED Admit(A, PutX)
=============================================================================
