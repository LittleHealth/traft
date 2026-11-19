------------------------ MODULE TRaftProofScenarios --------------------------
EXTENDS TRaftPaperScenarios, TRaftProofState
proofScenarioVars == <<scenarioVars, canonical>>
ProofScenarioInit == ScenarioInit /\ GhostInit
ProofScenarioNext == ScenarioNext /\ GhostNext
ProofScenarioSpec == ProofScenarioInit /\ [][ProofScenarioNext]_proofScenarioVars
=============================================================================
