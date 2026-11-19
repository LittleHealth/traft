------------------- MODULE TRaftClientWitnessRepresentation ------------------
EXTENDS TRaftEvidenceBatchInterpretation, TRaftClientCommandStability,
        TRaftFoldConcatProof, TRaftClientRealTimeStep

WitnessStateNow == [order |-> witness, db |-> abstractMachine, answers |-> abstractAnswers]
WitnessRepresentation ==
    /\ WitnessStateNow \in WitnessStates /\ UniqueOrder(witness)
    /\ WitnessSequential(WitnessStateNow)
    /\ WitnessPoint(WitnessStateNow) = AppliedPointState(EvidenceEntries)
    /\ Ids(witness) = EntryRequestIds(EvidenceEntries)

THEOREM SequenceUsesItsElementAlphabet ==
    ASSUME NEW S, NEW T, NEW order \in Seq(S), Ids(order) \subseteq T
    PROVE order \in Seq(T)
<1>1. Range(order) = Ids(order) /\ order \in Seq(Range(order))
    BY RangeEquality, SeqOfRange DEF Ids
<1> QED BY SeqMonotonic, <1>1

THEOREM WitnessRepresentationInitially == ClientInit => WitnessRepresentation
<1>1. ASSUME ClientInit
      PROVE WitnessRepresentation
    <2>1. witness = <<>> /\ abstractMachine = EmptyMachine /\ abstractAnswers = EmptyAnswers
          /\ EvidenceEntries = {}
        BY <1>1 DEF ClientInit, Init, EvidenceEntries
    <2>2. WitnessStateNow \in WitnessStates /\ UniqueOrder(witness)
          /\ Ids(witness) = {} /\ EntryRequestIds(EvidenceEntries) = {}
        BY SMT, EmptySeq, <2>1 DEF WitnessStateNow, WitnessStates, EmptyMachine, EmptyAnswers,
                                 UniqueOrder, Ids, EntryRequestIds
    <2>3. WitnessSequential(WitnessStateNow)
        BY FoldEmptySequence, <2>1 DEF WitnessSequential, WitnessStateNow, FoldExecuteOrder
    <2>4. WitnessPoint(WitnessStateNow) = AppliedPointState({})
        <3>1. WitnessStateNow.db = EmptyMachine
              /\ WitnessStateNow.answers = EmptyAnswers
              /\ Ids(WitnessStateNow.order) = {}
            BY ONLY SMT, <2>1, <2>2 DEF WitnessStateNow
        <3>2. WitnessCache(WitnessStateNow) = EmptyCache
            <4>1. DOMAIN WitnessCache(WitnessStateNow) = RequestIds
                  /\ DOMAIN EmptyCache = RequestIds
                BY ONLY SMT DEF WitnessCache, EmptyCache
            <4>2. \A id \in RequestIds : WitnessCache(WitnessStateNow)[id] = EmptyCache[id]
                <5>1. ASSUME NEW id \in RequestIds
                      PROVE WitnessCache(WitnessStateNow)[id] = EmptyCache[id]
                    <6>1. WitnessCache(WitnessStateNow)[id] =
                              [ready |-> id \in Ids(WitnessStateNow.order),
                               value |-> WitnessStateNow.answers[id]]
                        BY ONLY SMT, <5>1 DEF WitnessCache
                    <6>2. WitnessStateNow.answers[id] = Missing
                          /\ id \notin Ids(WitnessStateNow.order)
                        BY ONLY SMT, <3>1, <5>1 DEF EmptyAnswers
                    <6>3. EmptyCache[id] = [ready |-> FALSE, value |-> Missing]
                        BY ONLY SMT, <5>1 DEF EmptyCache
                    <6> QED BY ONLY IsaM("auto"), <6>1, <6>2, <6>3
                <5> QED BY ONLY <5>1
            <4> QED BY ONLY IsaM("auto"), <4>1, <4>2 DEF WitnessCache, EmptyCache
        <3>3. WitnessPoint(WitnessStateNow) = [db |-> EmptyMachine, cache |-> EmptyCache]
            BY ONLY SMT, <3>1, <3>2 DEF WitnessPoint
        <3> QED BY ONLY EmptyAppliedState, <3>3
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF WitnessRepresentation
<1> QED BY <1>1

THEOREM WitnessRepresentationFollowsEvidence ==
    ASSUME WitnessRepresentation, RequestIdentityState, RequestIdentityState', calls \subseteq calls',
           IsFiniteSet(EvidenceEntries'), EvidenceEntries' \subseteq Entries,
           PointLog(EvidenceEntries'), Coherent(EvidenceEntries'),
           EvidenceEntries \subseteq EvidenceEntries',
           \A e \in EvidenceEntries' : e.kind = "data" => e.value \in calls,
           \A e \in EvidenceEntries' \ EvidenceEntries : \A old \in EvidenceEntries : old.part <= e.part,
           ProofObserveLinearization
    PROVE WitnessRepresentation' /\ OrderPrefix(witness, witness')
<1>1. DEFINE initial == WitnessStateNow
            batch == FreshEvidenceBatch(EvidenceEntries, EvidenceEntries')
            result == Fold(SortedEntryOrder(batch), initial, LinearizationEntryStep)
<1>2. initial \in WitnessStates /\ UniqueOrder(initial.order) /\ WitnessSequential(initial)
      /\ WitnessPoint(initial) = AppliedPointState(EvidenceEntries)
    BY DEF WitnessRepresentation, initial, WitnessStateNow
<1>3. result \in WitnessStates /\ UniqueOrder(result.order)
      /\ OrderPrefix(initial.order, result.order) /\ WitnessSequential(result)
      /\ WitnessPoint(result) = AppliedPointState(EvidenceEntries')
      /\ Ids(result.order) = EntryRequestIds(EvidenceEntries')
    BY EvidenceBatchExtendsTheSequentialWitness, <1>2 DEF result, batch
<1>4. witness' = result.order /\ abstractMachine' = result.db /\ abstractAnswers' = result.answers
    BY DEF ProofObserveLinearization, SortedIncorporation, WitnessRepresentation,
           WitnessStateNow, initial, result, batch, FreshEvidenceBatch, EvidenceEntries
<1>5. WitnessStateNow' = result /\ result.order \in Seq(RequestIds)
      /\ Ids(result.order) \subseteq CalledIds
    BY <1>3, <1>4 DEF WitnessStateNow, WitnessStates, EntryRequestIds, CalledIds
<1>6. result.order \in Seq(CalledIds)
    BY SequenceUsesItsElementAlphabet, <1>5
<1>7. ExecutionFrom(calls, result.order, EmptyMachine, EmptyAnswers)
          = ExecutionFrom(calls', result.order, EmptyMachine, EmptyAnswers)
    BY ClientCallExtensionKeepsOldExecution, <1>6
<1>8. CurrentExecutionIdentity'
    BY ONLY PTL, CurrentExecutionIdentity
<1>9. WitnessSequential(WitnessStateNow)'
    BY CurrentExecutionIdentity, <1>3, <1>5, <1>7, <1>8
       DEF WitnessSequential, WitnessStateNow
<1> QED BY <1>3, <1>4, <1>5, <1>9 DEF WitnessRepresentation, initial, WitnessStateNow

THEOREM NewEvidenceCallsWereAlreadyInvoked ==
    ASSUME CommitEvidenceSound, Observe, ClientAction,
           \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls,
           \A e \in EvidenceEntries' : e.kind = "data" => e.value \in calls'
    PROVE \A e \in EvidenceEntries' : e.kind = "data" => e.value \in calls
<1>1. (\E q \in ClientCommands : Invoke(q)) \/ UNCHANGED <<calls, nextSequence>>
    BY OnlyInvocationChangesRequestIdentity
<1>2. CASE UNCHANGED <<calls, nextSequence>>
    BY <1>2
<1>3. CASE \E q \in ClientCommands : Invoke(q)
    <2>1. UNCHANGED ackMessages
        BY <1>3 DEF Invoke, protocolVars
    <2>2. UNCHANGED EvidenceEntries
        BY StutteringAcksKeepEvidenceEntries, <2>1
    <2> QED BY <2>2
<1> QED BY <1>1, <1>2, <1>3
=============================================================================
