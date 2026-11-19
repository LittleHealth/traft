---------------------- MODULE TRaftPotentialCoverageProof ---------------------
EXTENDS TRaftInvariantDefinitions, TRaftPotentialProof, TRaftCanonicalTransitionSupport, TRaftOriginFrames,
        TRaftAckSourceFrames, TRaftRetainedFrames, TRaftTermAndVoteProof
USE ParameterAssumptions, FormalFaultsDisabled DEF ParameterAssumptions, FormalFaultsDisabled

THEOREM FormalChangeIsAppendOrPublish ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE \A r \in Replicas : formal[r] \subseteq formal'[r] \/
        \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p)
<1>1. TypeOK /\ (FormalAnchorChanges \/ UNCHANGED formal)
    BY FormalAnchorActionProjection DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>2. \A c \in Replicas : \A v, k :
          (CreateEntry(c, v) \/ CreateSuccessor(c, v, k)) =>
              \A r \in Replicas : formal[r] \subseteq formal'[r]
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, TypeOK
<1>3. \A c \in Replicas : \A o : ReceiveEntry(c, o) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r]
    BY SMT, <1>1 DEF ReceiveEntry, TypeOK
<1>4. \A c \in Replicas : ConfirmProposal(c) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r] \/
              \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p)
    BY SMT, <1>1 DEF ConfirmProposal, TypeOK
<1>5. \A c \in Replicas : \A p : LearnConfirmation(c, p) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r] \/
              \E q \in retained[r] : q.epoch = term[r] /\ formal'[r] = Publish(r, q)
    BY SMT, <1>1 DEF LearnConfirmation, TypeOK
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5 DEF FormalAnchorChanges

THEOREM CurrentFormalEntryPinsProposal ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW e \in formal[r], e.term = term[r],
           NEW p \in retained[r], p.epoch = term[r]
    PROVE p.first \in formal[r]
<1>1. LastTerm(formal[r]) = term[r]
    BY CurrentTermEntryPinsSublogEpoch
<1>2. PICK q \in retained[r] : q.epoch = term[r] /\ Result(q) \subseteq formal[r]
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>3. p \in proposals /\ q \in proposals
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>4. p = q
    BY SMT, <1>2, <1>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>2, <1>4 DEF Result

THEOREM PublishPreservesOldPotentialAck ==
    ASSUME ProofInvariant, NEW a \in ackMessages, NEW e \in a.contents,
           MayChoose(a.epoch, e), NEW p \in retained[a.sender], p.epoch = term[a.sender]
    PROVE e \in Publish(a.sender, p) \cup RetainedContents(a.sender)
<1>1. a.sender \in Replicas /\ a.epoch \in Nat /\ term[a.sender] \in Nat
      /\ a.epoch <= term[a.sender] /\ e \in formal[a.sender] \cup RetainedContents(a.sender)
      /\ p \in proposals /\ a.epoch \in Terms /\ e \in IssuedEntries
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
        AckOrigin, TypeOK, PotentialCoverage, Terms, IssuedEntries
<1>2. CASE e \in RetainedContents(a.sender)
    BY <1>2
<1>3. CASE e \notin RetainedContents(a.sender)
    <2>1. e \in formal[a.sender]
        BY <1>1, <1>3
    <2>2. CASE a.epoch < p.epoch
        <3>1. e \in p.prefix
            BY <1>1, <2>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, PotentialPreservation
        <3> QED BY SMT, <2>1, <3>1 DEF Publish, Result
    <2>3. CASE a.epoch = p.epoch
        <3>1. PICK q \in retained[a.sender] :
                  a.contents = Result(q) \/ (a.contents = {a.target} /\ a.target.term = a.epoch)
            BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin
        <3>2. a.contents # Result(q)
            BY SMT, <1>3, <3>1 DEF RetainedContents
        <3>3. e.term = term[a.sender]
            BY SMT, <2>3, <3>1, <3>2
        <3>4. p.first \in formal[a.sender]
            BY CurrentFormalEntryPinsProposal, <1>1, <2>1, <3>3
        <3> QED BY <2>1, <3>4 DEF Publish
    <2> QED BY SMT, <1>1, <2>2, <2>3
<1> QED BY <1>2, <1>3

THEOREM OldAcknowledgementsKeepPotentialCoverage ==
    ASSUME ProofInvariant, ProtocolNext, StepFacts, term' \in [Replicas -> Nat],
           \A r \in Replicas : retained[r] \subseteq retained'[r]
    PROVE \A a \in ackMessages : \A e \in a.contents : MayChoose(a.epoch, e)' =>
        e \in formal'[a.sender] \cup RetainedContents(a.sender)'
<1>1. term \in [Replicas -> Nat] /\ \A a \in ackMessages : a.epoch \in Nat /\ a.sender \in Replicas
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, AckOrigin, Terms
<1>2. \A r \in Replicas : formal[r] \subseteq formal'[r] \/
          \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p)
    BY FormalChangeIsAppendOrPublish
<1>3. \A r \in Replicas : RetainedContents(r) \subseteq RetainedContents(r)'
    BY SMT DEF RetainedContents
<1>4. ASSUME NEW a \in ackMessages, NEW e \in a.contents, MayChoose(a.epoch, e)'
      PROVE e \in formal'[a.sender] \cup RetainedContents(a.sender)'
    <2>1. MayChoose(a.epoch, e)
        BY PossibleMajoritiesOnlyShrink, <1>1, <1>4
    <2>2. e \in formal[a.sender] \cup RetainedContents(a.sender)
        BY <1>4, <2>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, PotentialCoverage
    <2> QED BY SMT, PublishPreservesOldPotentialAck, <1>1, <1>2, <1>3, <1>4, <2>1, <2>2
<1> QED BY <1>4

THEOREM NewAcknowledgementsHaveCurrentCoverage ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE \A a \in ackMessages' \ ackMessages : \A e \in a.contents :
        e \in formal'[a.sender] \cup RetainedContents(a.sender)'
<1>1. (\E r \in Replicas : \E o : AckEntry(r, o))
          \/ (\E r \in Replicas : \E p : AckProposal(r, p)) \/ UNCHANGED ackMessages
    BY OnlyAckActionsChangeMessages
<1>2. \A r \in Replicas : \A o : AckEntry(r, o) =>
          \A a \in ackMessages' \ ackMessages : \A e \in a.contents : e \in formal'[a.sender]
    BY SMT DEF AckEntry, Ack
<1>3. \A r \in Replicas : \A p : AckProposal(r, p) =>
          \A a \in ackMessages' \ ackMessages : \A e \in a.contents : e \in RetainedContents(a.sender)'
    BY SMT DEF AckProposal, Ack, RetainedContents
<1> QED BY SMT, <1>1, <1>2, <1>3

THEOREM ExistingReportsKeepPotentialCoverage ==
    ASSUME ProofInvariant, StepFacts, term' \in [Replicas -> Nat]
    PROVE \A m \in reportMessages, a \in ackMessages' : \A e \in a.contents :
        a.sender = m.sender /\ a.epoch < m.epoch /\ MayChoose(a.epoch, e)' => e \in ReportContents(m)
<1>1. term \in [Replicas -> Nat]
      /\ (\A m \in reportMessages : m.sender \in Replicas /\ m.epoch \in Nat /\ m.epoch <= term[m.sender])
      /\ (\A a \in ackMessages : a.epoch \in Nat)
    <2>1. term \in [Replicas -> Terms]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. (\A m \in reportMessages : m.sender \in Replicas /\ m.epoch \in Terms
                  /\ m.epoch <= term[m.sender])
          /\ (\A a \in ackMessages : a.epoch \in Terms)
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
            AckOrigin, TermAndVoteFacts, ReportFences
    <2>3. Terms \subseteq Nat
        BY ONLY ParameterAssumptions DEF ParameterAssumptions
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1>2. ASSUME NEW m \in reportMessages, NEW a \in ackMessages', NEW e \in a.contents,
            a.sender = m.sender, a.epoch < m.epoch, MayChoose(a.epoch, e)'
      PROVE e \in ReportContents(m)
    <2>1. a \in ackMessages
        BY SMT, <1>1, <1>2 DEF StepFacts
    <2>2. MayChoose(a.epoch, e)
        BY PossibleMajoritiesOnlyShrink, <1>1, <1>2, <2>1
    <2> QED BY <1>2, <2>1, <2>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, PotentialCoverage
<1> QED BY <1>2

THEOREM NewReportHasPotentialCoverage ==
    ASSUME ProofInvariant, StepFacts, term' \in [Replicas -> Nat], ~MutDropPending,
           NEW r \in Replicas, NEW req, MakeReport(r, req)
    PROVE \A m \in reportMessages' \ reportMessages, a \in ackMessages' : \A e \in a.contents :
        a.sender = m.sender /\ a.epoch < m.epoch /\ MayChoose(a.epoch, e)' => e \in ReportContents(m)
<1>1. UNCHANGED ackMessages
      /\ \A m \in reportMessages' \ reportMessages : m.sender = r /\ m.entries = formal[r] /\ m.pending = retained[r]
    BY SMT DEF MakeReport
<1>2. term \in [Replicas -> Nat] /\ \A a \in ackMessages : a.epoch \in Nat
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, AckOrigin, Terms
<1>3. \A a \in ackMessages' : \A e \in a.contents : MayChoose(a.epoch, e)' => MayChoose(a.epoch, e)
    BY PossibleMajoritiesOnlyShrink, <1>1, <1>2
<1> QED BY SMT, <1>1, <1>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
    PotentialCoverage, ReportContents, RetainedContents

THEOREM PotentialCoverageInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE PotentialCoverage'
<1>1. ProofInvariant /\ ProtocolNext /\ StepFacts /\ ElectionInvariant'
    BY CandidateStepHasMonotonicFacts, ElectionInductiveStep
       DEF Inv, ProofInvariant, PreProvenanceInvariant, ProofNext, Next
<1>2. term' \in [Replicas -> Nat] /\ retained = [r \in Replicas |-> retained[r]]
    BY SMT, <1>1 DEF ElectionInvariant, ElectionTypes, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
<1>3. \A r \in Replicas : retained[r] \subseteq retained'[r]
    BY RetainedChangeHasCurrentEpoch, <1>1, <1>2
<1>4. \A a \in ackMessages' : \A e \in a.contents : MayChoose(a.epoch, e)' =>
          e \in formal'[a.sender] \cup RetainedContents(a.sender)'
    BY SMT, OldAcknowledgementsKeepPotentialCoverage, NewAcknowledgementsHaveCurrentCoverage, <1>1, <1>2, <1>3
<1>5. (\E r \in Replicas : \E req : MakeReport(r, req)) \/ UNCHANGED reportMessages
    BY ReportAnchorActionProjection, <1>1
<1>6. \A m \in reportMessages', a \in ackMessages' : \A e \in a.contents :
          a.sender = m.sender /\ a.epoch < m.epoch /\ MayChoose(a.epoch, e)' => e \in ReportContents(m)
    BY SMT, ExistingReportsKeepPotentialCoverage, NewReportHasPotentialCoverage, <1>1, <1>2, <1>5
<1> QED BY <1>4, <1>6 DEF PotentialCoverage
=============================================================================
