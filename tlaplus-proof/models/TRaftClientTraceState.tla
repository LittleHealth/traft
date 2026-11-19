---------------------- MODULE TRaftClientTraceState ----------------------
EXTENDS TRaftClientTraceInterface

\* Proof decomposition only. Every imported theorem is checked separately.
\* No executable action, observer, state predicate or target is strengthened.

\* These facts are established independently of the linearization witness.
\* No action uses this predicate as an enabling condition.
ClientTraceContext ==
    /\ LiftedSafety!Inv /\ DerivedPointLogs /\ DerivedRequestSources
    /\ RequestIdentityState /\ RequestHistoryState /\ IsFiniteSet(CalledIds)
    /\ ApplicationTypes /\ ApplicationMatchesAppliedSet /\ AppliedPrefixClosure
    /\ ReplySources /\ ReturnedMessagesHaveSource /\ ObserverClosure

THEOREM TraceContextHasSafety == ClientTraceContext => Safety
BY ONLY LiftedSafetyPredicateIdentity DEF ClientTraceContext, LiftedSafety!Inv

THEOREM ClientObserversAlwaysClosed ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []ObserverClosure
<1>1. ClientInit => ObserverClosure
    BY ObserversInitiallyClosed DEF ClientInit
<1>2. ObserverClosure /\ [ClientAction /\ Observe /\ Extra]_clientVars => ObserverClosure'
    BY ObservationEstablishesClosure, ObserverClosureStuttering DEF clientVars
<1> QED BY PTL, <1>1, <1>2 DEF ClientSpecification
=============================================================================
