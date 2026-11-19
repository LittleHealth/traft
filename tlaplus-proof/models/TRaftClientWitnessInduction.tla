--------------------- MODULE TRaftClientWitnessInduction ---------------------
EXTENDS TRaftClientLinearizationContext, TRaftClientWitnessStutter

\* The original induction statement and its proof are retained. This module
\* bounds the composition context independently of the temporal root.
THEOREM ClientWitnessInductiveStep ==
    ASSUME ClientTraceContext, ClientTraceContext', ClientWitnessInvariant,
           ClientAction, Observe, ProofObserveLinearization
    PROVE ClientWitnessInvariant'
<1>0. TraceContextProvidesEvidenceInputs'
    BY ONLY PTL, TraceContextProvidesEvidenceInputs
<1>1. RequestIdentityState /\ RequestIdentityState' /\ calls \subseteq calls'
      /\ IsFiniteSet(EvidenceEntries') /\ EvidenceEntries' \subseteq Entries
      /\ PointLog(EvidenceEntries') /\ Coherent(EvidenceEntries')
    BY CallsNeverShrinkForReplySources, <1>0
       DEF ClientTraceContext
<1>3. \A e \in EvidenceEntries' : e.kind = "data" => e.value \in calls'
    BY <1>0
<1>4. \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
    BY TraceContextProvidesEvidenceInputs
<1>5. \A e \in EvidenceEntries' : e.kind = "data" => e.value \in calls
    BY NewEvidenceCallsWereAlreadyInvoked, TraceContextHasSafety, <1>3, <1>4
       DEF ClientTraceContext, LiftedSafety!Inv, Safety
<1>6. EvidenceEntries \subseteq EvidenceEntries' /\ NewEvidenceFollowsOldPartitions
    BY TracedClientEvidenceOnlyGrowsInPartitionOrder
<1>7. WitnessRepresentation' /\ OrderPrefix(witness, witness')
    BY WitnessRepresentationFollowsEvidence, <1>1, <1>5, <1>6
       DEF ClientWitnessInvariant, NewEvidenceFollowsOldPartitions
<1>8. ReturnedIds \subseteq Ids(witness)
    BY TracedWitnessRepliesAndIdentities DEF ClientWitnessInvariant, ReturnedWitnessAgreement
<1>9. witness \in Seq(RequestIds) /\ witness' \in Seq(RequestIds)
      /\ UniqueOrder(witness') /\ Ids(witness') = EvidenceRequestIds'
    BY <1>7 DEF ClientWitnessInvariant, WitnessRepresentation, WitnessStateNow,
               WitnessStates, EntryRequestIds, EvidenceRequestIds
<1>10. RealTimeIn(history', witness')
    BY ClientEventsPreserveRealTime, TraceContextHasSafety, <1>4, <1>7, <1>8, <1>9
       DEF ClientTraceContext, ClientWitnessInvariant, LiftedSafety!Inv, Safety
<1> QED BY <1>7, <1>10 DEF ClientWitnessInvariant
=============================================================================
