-------------------- MODULE TRaftClientApplicationTemporal -------------------
EXTENDS TRaftClientPartitionTemporal, TRaftClientApplicationStutter,
        TRaftPointLiftSourceInterface

DerivedRequestSources == CanonicalDataFrom(DerivedCanonical, calls)

\* The request-source and partition inductions share the same PointLift
\* substitution. Their independently checked source theorems remain required.
THEOREM SourceLiftParameters ==
    /\ PointLift!ParameterAssumptions /\ PointLift!SentinelSeparation
    /\ PointLift!ClientParameters
BY ONLY PointLiftParameters

THEOREM SourceLiftStateIdentities ==
    /\ (PointLift!ProofInvariant <=> PointLift!ProofInvariant)
    /\ (PointLift!CanonicalShape <=> PointLift!CanonicalShape)
BY ONLY SMT

THEOREM ClientRequestSourcesInitially == ClientInit => DerivedRequestSources
<1>1. ASSUME ClientInit
      PROVE DerivedRequestSources
    <2>1. DerivedCanonical = [t \in Terms |-> {}]
        BY CoreInitializationLifts, <1>1 DEF ClientInit, LiftedInit
    <2> QED BY SMT, <2>1 DEF DerivedRequestSources, CanonicalDataFrom, LogDataFrom
<1> QED BY <1>1

THEOREM ClientRequestSourcesStep ==
    ASSUME DerivedRequestSources, LiftedSafety!Inv, ClientAction, Observe, TypeOK'
    PROVE DerivedRequestSources'
<1>1. PointLift!ProofInvariant /\ ElectionSafety /\ term' \in [Replicas -> Terms]
    BY SourceLiftStateIdentities, PointLiftStateIdentities, LiftedSafetyPredicateIdentity
       DEF LiftedSafety!Inv, Safety, TypeOK
<1>2. PointLift!GhostNext
    BY ClientObservationLiftsCanonical
<1> QED BY PointLift!ClientRequestSourcesInductiveStep, SourceLiftParameters,
       SourceLiftInterfaceIdentities, <1>1, <1>2
       DEF DerivedRequestSources, PointLift!ParameterAssumptions,
           PointLift!SentinelSeparation, PointLift!ClientParameters

THEOREM ClientRequestSourcesStutter ==
    ASSUME DerivedRequestSources, UNCHANGED clientVars
    PROVE DerivedRequestSources'
BY SMT DEF DerivedRequestSources, DerivedCanonical, clientVars, vars, protocolVars,
   observerVars, localClientVars

THEOREM ClientRequestSourcesAlways ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []DerivedRequestSources
<1>1. ClientSpecification(Extra) => []LiftedSafety!Inv /\ []TypeOK
    BY PTL, ClientTemporalRefinement, ProtocolInvariant, ProtocolSafety DEF Safety
<1>2. ClientInit => DerivedRequestSources
    BY ClientRequestSourcesInitially
<1>3. DerivedRequestSources /\ LiftedSafety!Inv /\ TypeOK'
      /\ [ClientAction /\ Observe /\ Extra]_clientVars => DerivedRequestSources'
    BY ClientRequestSourcesStep, ClientRequestSourcesStutter
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification

THEOREM DerivedSourcesReachApplication ==
    ASSUME DerivedRequestSources, LiftedSafety!Inv, RequestIdentityState
    PROVE ClientApplicationSources /\ FormalDataFrom(formal, calls)
<1>1. PointLift!CanonicalShape /\ calls \subseteq ClientCommands
    BY SourceLiftStateIdentities, PointLiftStateIdentities
       DEF LiftedSafety!Inv, LiftedSafety!ProofInvariant,
           LiftedSafety!PreProvenanceInvariant, LiftedSafety!RecoveryInvariant, RequestIdentityState
<1>2. FormalDataFrom(formal, calls)
    BY PointLift!CanonicalRequestSourcesReachReplicas, SourceLiftParameters,
       SourceLiftInterfaceIdentities, <1>1
       DEF DerivedRequestSources, PointLift!ParameterAssumptions,
           PointLift!SentinelSeparation, PointLift!ClientParameters
<1> QED BY <1>1, <1>2 DEF ClientApplicationSources, FormalDataFrom, LogDataFrom

THEOREM ClientApplicationFactsAlways ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => [](ApplicationTypes /\ ReadyIdsMatchApplied)
<1>1. ClientSpecification(Extra) => []ClientApplicationSources /\ []TypeOK
    BY PTL, ClientRequestSourcesAlways, ClientRequestIdentityAlways,
       ClientTemporalRefinement, ProtocolInvariant, ProtocolSafety, DerivedSourcesReachApplication
       DEF LiftedSafety!Inv, Safety
<1>2. ClientInit => ApplicationTypes /\ ReadyIdsMatchApplied
    BY ApplicationTypesInitially
<1>3. ApplicationTypes /\ ReadyIdsMatchApplied /\ ClientApplicationSources /\ TypeOK
      /\ [ClientAction /\ Observe /\ Extra]_clientVars =>
          ApplicationTypes' /\ ReadyIdsMatchApplied'
    <2>1. ApplicationTypes /\ ReadyIdsMatchApplied /\ ClientApplicationSources /\ TypeOK
          /\ ClientAction => ApplicationTypes' /\ ReadyIdsMatchApplied'
        BY ClientApplicationFactsInductiveStep
    <2>2. UNCHANGED clientVars => UNCHANGED <<machine, cache, applied>>
        BY ONLY SMT DEF clientVars, vars, protocolVars, localClientVars
    <2>3. ApplicationTypes /\ ReadyIdsMatchApplied /\ UNCHANGED <<machine, cache, applied>>
          => ApplicationTypes' /\ ReadyIdsMatchApplied'
        BY ONLY ClientApplicationFactsStutter
    <2> QED BY ONLY <2>1, <2>2, <2>3
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification

THEOREM ClientCacheHasAppliedRequestAlways ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []CacheHasAppliedRequest
<1>1. ClientSpecification(Extra) =>
          []ReadyIdsMatchApplied /\ []RequestIdentityState /\ []AppliedEntriesPreserved
          /\ []FormalDataFrom(formal, calls)
    BY PTL, ClientApplicationFactsAlways, ClientRequestIdentityAlways,
       ClientRequestSourcesAlways, DerivedSourcesReachApplication,
       ClientTemporalRefinement, ProtocolInvariant, ProtocolSafety DEF Safety
<1>2. ReadyIdsMatchApplied /\ RequestIdentityState /\ AppliedEntriesPreserved
      /\ FormalDataFrom(formal, calls) => CacheHasAppliedRequest
    BY ReadyIdentityHasTheOriginalCommand DEF FormalDataFrom, LogDataFrom
<1> QED BY PTL, <1>1, <1>2
=============================================================================
