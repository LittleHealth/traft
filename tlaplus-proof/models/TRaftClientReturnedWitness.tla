----------------------- MODULE TRaftClientReturnedWitness --------------------
EXTENDS TRaftClientWitnessRepresentation, TRaftClientEvidenceAnswers

ClientAnswerContext ==
    /\ ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique
    /\ AppliedEntriesPreserved /\ AppliedPrefixClosure /\ ApplicationMatchesAppliedSet
    /\ RequestIdentityState
    /\ \A t \in Terms : PointLog(canonical[t])
    /\ \A t \in Terms : \A e \in canonical[t] : e.kind = "data" => e.value \in calls
    /\ \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls
ReturnedWitnessAgreement ==
    /\ ReturnedIds \subseteq Ids(witness)
    /\ \A m \in returned : m.value = abstractAnswers[m.id]

THEOREM EveryReplyMatchesItsEvidenceWitness ==
    ASSUME ClientAnswerContext, WitnessRepresentation, ReplySources,
           NEW m \in replyMessages
    PROVE m.id \in Ids(witness) /\ m.value = abstractAnswers[m.id]
<1>1. PICK q \in calls : q.id = m.id /\ m.sender \in Replicas
          /\ cache[m.sender][m.id].ready /\ m.value = cache[m.sender][m.id].value
    BY DEF ReplySources, ReplyHasDurableSource
<1>2. q.id \in RequestIds
    BY <1>1 DEF ClientAnswerContext, RequestIdentityState, ClientCommands
<1>3. AppliedCache(EvidenceEntries)[q.id] = cache[m.sender][q.id]
    BY ReadyAnswerMatchesGlobalEvidenceInterpretation, <1>1 DEF ClientAnswerContext
<1>4. WitnessCache(WitnessStateNow) = AppliedCache(EvidenceEntries)
    BY DEF WitnessRepresentation, WitnessPoint, AppliedPointState
<1>5. AppliedCache(EvidenceEntries)[q.id] =
          [ready |-> q.id \in Ids(witness), value |-> abstractAnswers[q.id]]
    BY <1>2, <1>4 DEF WitnessCache, WitnessStateNow
<1> QED BY ONLY <1>1, <1>3, <1>5

THEOREM ReturnedRepliesMatchTheirEvidenceWitness ==
    (ClientAnswerContext /\ WitnessRepresentation /\ ReplySources /\ ReturnedMessagesHaveSource)
        => ReturnedWitnessAgreement
<1>1. ASSUME ClientAnswerContext, WitnessRepresentation, ReplySources, ReturnedMessagesHaveSource,
            NEW m \in returned
      PROVE m.id \in Ids(witness) /\ m.value = abstractAnswers[m.id]
    <2>1. m \in replyMessages
        BY <1>1 DEF ReturnedMessagesHaveSource
    <2> QED BY EveryReplyMatchesItsEvidenceWitness, <1>1, <2>1
<1> QED BY <1>1 DEF ReturnedWitnessAgreement, ReturnedIds
=============================================================================
