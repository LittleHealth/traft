---------------------- MODULE TRaftClientWitnessStutter ----------------------
EXTENDS TRaftClientWitnessRepresentation

ClientWitnessInvariant == WitnessRepresentation /\ RealTimeIn(history, witness)

THEOREM ClientWitnessInitially == ClientInit => ClientWitnessInvariant
<1>1. ClientInit => WitnessRepresentation
    BY WitnessRepresentationInitially
<1>2. ClientInit => RealTimeIn(history, witness)
    BY SMT DEF ClientInit, RealTimeIn
<1> QED BY <1>1, <1>2 DEF ClientWitnessInvariant

THEOREM WitnessFrameComponents ==
    UNCHANGED <<calls, history, witness, abstractMachine, abstractAnswers, commitHistory>> =>
      /\ calls' = calls /\ history' = history /\ witness' = witness
      /\ WitnessStateNow' = WitnessStateNow /\ EvidenceEntries' = EvidenceEntries
BY ONLY SMT DEF WitnessStateNow, EvidenceEntries

\* Keep the state-dependent higher-order fold behind its separately proved
\* explicit-parameter identity. No fold definition or protocol action changes.
THEOREM SequentialWitnessStutters ==
    ASSUME WitnessStateNow \in WitnessStates, WitnessSequential(WitnessStateNow),
           calls' = calls, WitnessStateNow' = WitnessStateNow
    PROVE WitnessSequential(WitnessStateNow)'
<1>0. WitnessStateNow \in WitnessStates /\ WitnessSequential(WitnessStateNow)
      /\ calls' = calls /\ WitnessStateNow' = WitnessStateNow
    OBVIOUS
<1>1. WitnessStateNow.order \in Seq(RequestIds)
      /\ WitnessStateNow'.order \in Seq(RequestIds)
    BY ONLY SMT, <1>0 DEF WitnessStates
<1>2. ExecutionFrom(calls, WitnessStateNow.order, EmptyMachine, EmptyAnswers)
          = ExecutionFrom(calls', WitnessStateNow.order, EmptyMachine, EmptyAnswers)
    BY ONLY SMT, <1>0
<1>3. CurrentExecutionIdentity'
    BY ONLY PTL, CurrentExecutionIdentity
<1> QED BY ONLY CurrentExecutionIdentity, <1>0, <1>1, <1>2, <1>3
    DEF WitnessSequential

THEOREM ClientWitnessStutters ==
    ASSUME ClientWitnessInvariant, UNCHANGED clientVars
    PROVE ClientWitnessInvariant'
<1>0. UNCHANGED <<calls, history, witness, abstractMachine, abstractAnswers, commitHistory>>
    BY DEF clientVars, vars, observerVars, localClientVars, witnessVars
<1>1. calls' = calls /\ history' = history /\ witness' = witness
      /\ WitnessStateNow' = WitnessStateNow /\ EvidenceEntries' = EvidenceEntries
    BY ONLY WitnessFrameComponents, <1>0
<1>2. WitnessSequential(WitnessStateNow)'
    BY SequentialWitnessStutters, <1>1 DEF ClientWitnessInvariant, WitnessRepresentation
<1>3. WitnessStateNow' \in WitnessStates /\ UniqueOrder(witness')
      /\ WitnessPoint(WitnessStateNow') = AppliedPointState(EvidenceEntries')
      /\ Ids(witness') = EntryRequestIds(EvidenceEntries')
    BY SMT, <1>1 DEF ClientWitnessInvariant, WitnessRepresentation
<1>4. RealTimeIn(history', witness')
    BY SMT, <1>1 DEF ClientWitnessInvariant
<1> QED BY <1>2, <1>3, <1>4 DEF ClientWitnessInvariant, WitnessRepresentation
=============================================================================
