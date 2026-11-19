----------------------- MODULE TRaftClientLinearizability --------------------
EXTENDS TRaftClientWitnessInduction, TRaftClientHistoryCompletion,
        TRaftClientSpecificationProof

THEOREM ClientWitnessAlways ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup
    PROVE ProofClientSpec => []ClientWitnessInvariant
<1>1. ProofClientSpec => []ClientTraceContext
    BY ClientTraceContextAlways DEF ProofClientSpec
<1>2. ClientInit => ClientWitnessInvariant
    BY ClientWitnessInitially
<1>3. ClientWitnessInvariant /\ ClientTraceContext /\ ClientTraceContext'
      /\ [ClientAction /\ Observe /\ ProofObserveLinearization]_clientVars => ClientWitnessInvariant'
    BY ClientWitnessInductiveStep, ClientWitnessStutters
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ProofClientSpec, ClientSpecification

\* This target uses the explicit logged-read client protocol.  Its conclusion
\* is an independent sequential-history predicate, with no reference to the
\* ACK observer or chosen witness. Imported obligations must also be checked.
THEOREM ProofClientLinearizability ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup
    PROVE ProofClientSpec => []FoldHistoryLinearizable
<1>1. ProofClientSpec => []ClientTraceContext /\ []ClientWitnessInvariant
    <2>1. ProofClientSpec => []ClientTraceContext
        BY ClientTraceContextAlways DEF ProofClientSpec
    <2>2. ProofClientSpec => []ClientWitnessInvariant
        BY ClientWitnessAlways
    <2> QED BY ONLY PTL, <2>1, <2>2
<1>2. ClientTraceContext /\ ClientWitnessInvariant => FoldHistoryLinearizable
    <2>1. ASSUME ClientTraceContext, ClientWitnessInvariant
          PROVE FoldHistoryLinearizable
        <3>1. Ids(witness) \subseteq CalledIds /\ ReturnedWitnessAgreement
            BY TracedWitnessRepliesAndIdentities, <2>1 DEF ClientWitnessInvariant
        <3> QED BY SequentialWitnessImpliesIndependentHistory, <2>1, <3>1
            DEF ClientTraceContext, ClientWitnessInvariant, ReturnedWitnessAgreement
    <2> QED BY <2>1
<1> QED BY PTL, <1>1, <1>2
THEOREM ClientLinearizability ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup
    PROVE ClientSpec => []FoldHistoryLinearizable
BY PTL, ProofClientLinearizability, SharedClientSpecificationIdentity
=============================================================================
