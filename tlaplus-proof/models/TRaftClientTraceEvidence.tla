---------------------- MODULE TRaftClientTraceEvidence ----------------------
EXTENDS TRaftClientTraceState

\* Proof decomposition only. Every imported theorem is checked separately.
\* No executable action, observer, state predicate or target is strengthened.

THEOREM TraceContextProvidesAnswerContext ==
    ClientTraceContext => PointLift!ClientAnswerContext
<1>1. ASSUME ClientTraceContext
      PROVE PointLift!ClientAnswerContext
    <2>1. FormalDataFrom(formal, calls)
        BY DerivedSourcesReachApplication, <1>1 DEF ClientTraceContext
    <2> QED BY TraceLiftStateIdentity, TraceLiftInterfaceIdentities,
                LiftedSafetyPredicateIdentity, <1>1, <2>1
        DEF ClientTraceContext, PointLift!ClientAnswerContext, LiftedSafety!Inv, Safety,
            DerivedPointLogs, CanonicalPointLogs, DerivedRequestSources, CanonicalDataFrom,
            FormalDataFrom, LogDataFrom
<1> QED BY <1>1

THEOREM TraceContextProvidesEvidenceInputs ==
    ClientTraceContext =>
      /\ IsFiniteSet(EvidenceEntries) /\ EvidenceEntries \subseteq Entries
      /\ PointLog(EvidenceEntries) /\ Coherent(EvidenceEntries)
      /\ \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
<1>1. ASSUME ClientTraceContext
      PROVE IsFiniteSet(EvidenceEntries) /\ EvidenceEntries \subseteq Entries
            /\ PointLog(EvidenceEntries) /\ Coherent(EvidenceEntries)
            /\ \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
    <2>1. PointLift!ClientAnswerContext
        BY TraceContextProvidesAnswerContext, <1>1
    <2> QED BY PointLift!EvidenceEntriesAreFiniteAndTyped, PointLift!EvidenceEntriesAreCoherent,
                PointLift!EvidenceEntriesRespectPointPartitions, PointLift!EvidenceDataHasAnActualCall,
                TraceLiftParameters, TraceLiftInterfaceIdentities, <2>1
        DEF PointLift!ClientAnswerContext, PointLift!ClientParameters, PointLift!ParameterAssumptions, PointLift!SentinelSeparation
<1> QED BY <1>1

THEOREM TracedClientStepProjects ==
    (ClientTraceContext /\ ClientAction /\ Observe) => [Next]_vars
<1>1. ClientAction => [ProtocolNext]_protocolVars
    BY ClientActionProjects
<1> QED BY ClosedObservationStutters, <1>1 DEF ClientTraceContext, Next, vars

THEOREM TracedClientEvidenceOnlyGrowsInPartitionOrder ==
    ASSUME ClientTraceContext, ClientTraceContext', ClientAction, Observe
    PROVE EvidenceEntries \subseteq EvidenceEntries' /\ NewEvidenceFollowsOldPartitions
<1>0. OrderLiftStateIdentity'
    BY ONLY PTL, OrderLiftStateIdentity
<1>1. [Next]_vars /\ PointLift!Inv /\ PointLift!Inv'
    BY TracedClientStepProjects, OrderLiftStateIdentity, <1>0 DEF ClientTraceContext
<1>2. EvidenceEntries \subseteq EvidenceEntries'
    <2>1. ObservationEquations
        BY ObserveHasEquations
    <2>2. commitHistory \subseteq commitHistory'
        BY ONLY SMT, <2>1 DEF ObservationEquations
    <2> QED BY ONLY SMT, <2>2 DEF EvidenceEntries
<1>3. CASE Next
    BY PointLift!FirstEvidenceFormationRespectsPartitionOrder, OrderLiftParameters,
       OrderLiftInterfaceIdentities, <1>1, <1>2, <1>3
       DEF PointLift!ParameterAssumptions, PointLift!SentinelSeparation,
           PointLift!FormalFaultsDisabled, PointLift!ClientParameters
<1>4. CASE UNCHANGED vars
    BY <1>2, <1>4 DEF NewEvidenceFollowsOldPartitions, EvidenceEntries, vars, observerVars
<1> QED BY <1>1, <1>3, <1>4
=============================================================================
