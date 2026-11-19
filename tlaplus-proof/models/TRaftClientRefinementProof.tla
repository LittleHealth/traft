---------------------- MODULE TRaftClientRefinementProof ---------------------
EXTENDS TRaftProjectionProof, TRaftObserverClosureProof

\* Extra may be the ACK-based witness observer, including its recursive TLC
\* implementation. This theorem is uniform in that action; it does not read
\* witness variables or require a property of the witness to project behavior.
THEOREM ClientTemporalRefinement ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => Spec
<1>1. ClientInit => Init /\ ObserverClosure
    BY ClientInitializationProjects, ObserversInitiallyClosed
<1>2. [ClientAction /\ Observe /\ Extra]_clientVars /\ ObserverClosure => ObserverClosure'
    BY SMT, ObservationEstablishesClosure, ObserverClosureStuttering DEF clientVars
<1>3. ClientSpecification(Extra) => []ObserverClosure
    BY PTL, <1>1, <1>2 DEF ClientSpecification
<1>4. ObserverClosure /\ ClientAction /\ Observe /\ Extra => [Next]_vars
    BY SMT, ClientActionProjects, ClosedObservationStutters DEF Next, vars
<1>5. ObserverClosure /\ [ClientAction /\ Observe /\ Extra]_clientVars => [Next]_vars
    BY SMT, <1>4 DEF clientVars
<1> QED BY PTL, <1>1, <1>3, <1>5 DEF ClientSpecification, Spec
=============================================================================
