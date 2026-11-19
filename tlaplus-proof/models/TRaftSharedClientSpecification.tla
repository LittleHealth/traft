--------------------- MODULE TRaftSharedClientSpecification ------------------
EXTENDS TRaftClientLinearizationState

\* Both the executable finite model and the proof use this exact observer.
\* It assigns only witness variables; ClientAction cannot read those variables.
\* The independent recursive history checker remains in TRaftClients.
ObserveLinearization == ProofObserveLinearization
ClientNext == ClientAction /\ Observe /\ ObserveLinearization
ClientSpec == ClientSpecification(ObserveLinearization)
ProjectsToProtocol == [][Next]_vars
=============================================================================
