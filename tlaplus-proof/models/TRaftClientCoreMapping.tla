------------------------- MODULE TRaftClientCoreMapping ----------------------
EXTENDS TRaftBoundedObserverRefinement, TRaftClientRefinementProof

\* The client projection forgets application/client variables. The bounded
\* protocol projection keeps physical state and closes observer epochs upward.
THEOREM BoundedClientRefinesUnboundedCore ==
    ASSUME MaxTerm \in Nat \ {0}, Absent \notin Infinite!ProposalRecords,
           NEW ACTION Extra
    PROVE ClientSpecification(Extra) => MappedCore!Spec
<1>1. ClientSpecification(Extra) => Spec
    BY ClientTemporalRefinement
<1>2. Spec => MappedCore!Spec
    BY UnboundedCoreRefinement
<1> QED BY PTL, <1>1, <1>2
=============================================================================
