---------------------- MODULE TRaftClientLinearizationContext ----------------------
EXTENDS TRaftClientTraceEvidence

\* Proof decomposition only. Every imported theorem is checked separately.
\* No executable action, observer, state predicate or target is strengthened.

THEOREM ClientTraceContextAlways ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []ClientTraceContext
<1>1. ClientSpecification(Extra) =>
          []LiftedSafety!Inv /\ []DerivedPointLogs /\ []DerivedRequestSources
          /\ []RequestIdentityState /\ []RequestHistoryState /\ []IsFiniteSet(CalledIds)
    BY PTL, ClientTemporalRefinement, ProtocolInvariant, ClientPointLogsAlways,
       ClientRequestSourcesAlways, ClientRequestIdentityAlways, ClientHistorySourcesAlways,
       ClientCalledIdentitiesAlwaysFinite
<1>2. ClientSpecification(Extra) =>
          []ApplicationTypes /\ []ApplicationMatchesAppliedSet /\ []AppliedPrefixClosure
          /\ []ReplySources /\ []ReturnedMessagesHaveSource /\ []ObserverClosure
    BY PTL, ClientApplicationFactsAlways, ClientApplicationInterpretationAlways,
       ClientTemporalRefinement, ApplicationPrefixesAlwaysClosed,
       ClientRepliesHaveDurableSources, ClientObserversAlwaysClosed
<1> QED BY PTL, <1>1, <1>2 DEF ClientTraceContext

THEOREM TracedWitnessRepliesAndIdentities ==
    (ClientTraceContext /\ WitnessRepresentation) =>
      /\ Ids(witness) \subseteq CalledIds /\ ReturnedWitnessAgreement
<1>1. ASSUME ClientTraceContext, WitnessRepresentation
      PROVE Ids(witness) \subseteq CalledIds /\ ReturnedWitnessAgreement
    <2>1. PointLift!ClientAnswerContext
          /\ \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
        BY TraceContextProvidesAnswerContext, TraceContextProvidesEvidenceInputs, <1>1
    <2>2. ReturnedWitnessAgreement
        BY PointLift!ReturnedRepliesMatchTheirEvidenceWitness, TraceLiftParameters,
           TraceLiftInterfaceIdentities, <1>1, <2>1
           DEF ClientTraceContext, PointLift!ClientParameters, PointLift!ParameterAssumptions, PointLift!SentinelSeparation
    <2> QED BY <1>1, <2>1, <2>2
        DEF WitnessRepresentation, EntryRequestIds, CalledIds
<1> QED BY <1>1
=============================================================================
