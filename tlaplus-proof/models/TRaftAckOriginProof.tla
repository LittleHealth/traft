-------------------------- MODULE TRaftAckOriginProof -------------------------
EXTENDS TRaftInvariantDefinitions, TRaftCanonicalTransitionSupport,
        TRaftAckSourceFrames, TRaftRetainedFrames, TRaftTermAndVoteProof

AckOriginRecord(a, R, T, C) ==
    /\ a.sender \in Replicas /\ a.receiver \in Replicas
    /\ a.epoch \in Terms \ {0} /\ a.epoch <= T[a.sender]
    /\ a.contents \subseteq C[a.epoch]
    /\ \E p \in R[a.sender] :
         /\ p.epoch = a.epoch /\ p.owner = a.receiver
         /\ \/ a.contents = Result(p)
            \/ /\ a.contents = {a.target} /\ a.target.term = a.epoch
               /\ a.target.part >= p.first.part

THEOREM OldAckOriginSurvivesGrowth ==
    ASSUME NEW a, AckOriginRecord(a, retained, term, canonical),
           term \in [Replicas -> Nat], term' \in [Replicas -> Nat],
           \A r \in Replicas : term[r] <= term'[r] /\ retained[r] \subseteq retained'[r],
           \A t \in Terms : canonical[t] \subseteq canonical'[t]
    PROVE AckOriginRecord(a, retained', term', canonical')
BY SMT DEF AckOriginRecord, Terms

THEOREM NormalAcknowledgementHasAnchor ==
    ASSUME ProofInvariant, ElectionSafety, NEW r \in Replicas, NEW o, AckEntry(r, o)
    PROVE \E p \in retained[r] :
        p.epoch = o.epoch /\ p.owner = o.owner /\ o.entry.part >= p.first.part
<1>1. o \in offers /\ o.entry \in formal[r] /\ o.epoch = term[r]
    BY DEF AckEntry
<1>2. PICK v \in leaderViews : v.node = o.owner /\ v.epoch = o.epoch
          /\ o.entry \in v.entries /\ o.entry.term = o.epoch
    BY <1>1 DEF ProofInvariant, OfferProvenance
<1>3. LastTerm(formal[r]) = o.epoch /\ formal[r] \subseteq canonical[o.epoch]
    BY CurrentTermEntryPinsSublogEpoch, <1>1, <1>2
<1>4. PICK p \in retained[r] : p.epoch = o.epoch /\ Result(p) \subseteq formal[r]
    BY SMT, <1>1, <1>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>5. p \in proposals /\ p.epoch \in Terms \ {0} /\ p.first \in Entries
      /\ o.entry \in Entries
    BY SMT, <1>1, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>6. [node |-> p.owner, epoch |-> p.epoch] \in winners
      /\ [node |-> v.node, epoch |-> v.epoch] \in winners
    BY <1>2, <1>5 DEF ProofInvariant, PreProvenanceInvariant, ControlInvariant,
       ProposalProvenance, OwnedEpochs, LeaderHistoryInvariant, LeaderViewCertificates
<1>7. p.owner = o.owner
    BY SMT, <1>2, <1>4, <1>6 DEF ElectionSafety
<1>8. \A x \in p.prefix : x.term \in Nat /\ x.term < p.epoch
    BY SMT, <1>5 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, Entries, Terms, PrefixEvidenceInvariant, RecoveryProposalBoundaries
<1>9. o.entry \notin p.prefix
    BY SMT, <1>2, <1>4, <1>5, <1>8 DEF Entries, Terms
<1>10. \A x \in canonical[o.epoch] \ Result(p) : x.part >= p.first.part
    BY <1>4, <1>5 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>11. o.entry.part >= p.first.part
    BY SMT, <1>1, <1>3, <1>5, <1>9, <1>10 DEF Result, Entries, Partitions
<1> QED BY <1>4, <1>7, <1>11

THEOREM NewNormalAckOrigin ==
    ASSUME ProofInvariant, ElectionSafety,
           \A t \in Terms : canonical[t] \subseteq canonical'[t],
           NEW r \in Replicas, NEW o, AckEntry(r, o)
    PROVE AckOriginRecord(Ack(r, o.owner, o.epoch, o.entry, {o.entry}), retained', term', canonical')
<1>1. PICK p \in retained[r] : p.epoch = o.epoch /\ p.owner = o.owner
          /\ o.entry.part >= p.first.part
    BY NormalAcknowledgementHasAnchor
<1>2. o.entry.term = o.epoch /\ o.epoch = term[r] /\ o.entry \in formal[r]
      /\ o.owner \in Replicas /\ o.epoch \in Terms \ {0}
    BY SMT DEF AckEntry, ProofInvariant, OfferProvenance, CanonicalViewLinks,
        PreProvenanceInvariant, RecoveryInvariant, TypeOK, Entries, Terms,
        LeaderHistoryInvariant, PastLeaderViews
<1>3. formal[r] \subseteq canonical[o.epoch]
    BY CurrentTermEntryPinsSublogEpoch, <1>2
<1>4. UNCHANGED <<retained, term>> /\ o.entry \in canonical'[o.epoch]
    BY SMT, <1>2, <1>3 DEF AckEntry
<1> QED BY SMT, <1>1, <1>2, <1>4 DEF AckOriginRecord, Ack, Terms

THEOREM NewRecoveryAckOrigin ==
    ASSUME ProofInvariant, \A t \in Terms : canonical[t] \subseteq canonical'[t],
           NEW r \in Replicas, NEW p, AckProposal(r, p)
    PROVE AckOriginRecord(Ack(r, p.owner, p.epoch, p.first, Result(p)), retained', term', canonical')
<1>1. p \in retained[r] /\ term[r] = p.epoch /\ UNCHANGED <<retained, term>>
    BY DEF AckProposal
<1>2. p \in proposals /\ p.owner \in Replicas /\ p.epoch \in Terms \ {0}
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>3. Result(p) \subseteq canonical[p.epoch]
    BY <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>4. Result(p) \subseteq canonical'[p.epoch]
    BY <1>2, <1>3
<1> QED BY SMT, <1>1, <1>2, <1>4 DEF AckOriginRecord, Ack, Terms

THEOREM AckOriginInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE AckOrigin'
<1>1. ProofInvariant /\ ElectionSafety /\ ProtocolNext /\ GhostNext /\ StepFacts
      /\ ElectionInvariant'
    BY CandidateStepHasMonotonicFacts, ElectionInductiveStep
       DEF Inv, Safety, ProofNext, Next, ProofInvariant, PreProvenanceInvariant
<1>2. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
      /\ retained = [r \in Replicas |-> retained[r]]
    <2>1. term \in [Replicas -> Terms] /\ retained \in [Replicas -> SUBSET proposals]
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. term' \in [Replicas -> Terms]
        BY <1>1 DEF ElectionInvariant, ElectionTypes
    <2>3. Terms \subseteq Nat
        BY ONLY ParameterAssumptions DEF ParameterAssumptions
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1>3. (\A r \in Replicas : term[r] <= term'[r] /\ retained[r] \subseteq retained'[r])
      /\ (\A t \in Terms : canonical[t] \subseteq canonical'[t])
    BY SMT, RetainedChangeHasCurrentEpoch, <1>1, <1>2 DEF StepFacts, GhostNext
<1>4. \A a \in ackMessages : AckOriginRecord(a, retained', term', canonical')
    BY OldAckOriginSurvivesGrowth, <1>1, <1>2, <1>3
       DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin, AckOriginRecord
<1>5. (\E r \in Replicas : \E o : AckEntry(r, o))
          \/ (\E r \in Replicas : \E p : AckProposal(r, p)) \/ UNCHANGED ackMessages
    BY OnlyAckActionsChangeMessages, <1>1
<1>6. ASSUME NEW r \in Replicas, NEW o, AckEntry(r, o)
      PROVE \A a \in ackMessages' : AckOriginRecord(a, retained', term', canonical')
    <2>1. AckOriginRecord(Ack(r, o.owner, o.epoch, o.entry, {o.entry}), retained', term', canonical')
        BY NewNormalAckOrigin, <1>1, <1>3, <1>6
    <2> QED BY SMT, <1>4, <1>6, <2>1 DEF AckEntry
<1>7. ASSUME NEW r \in Replicas, NEW p, AckProposal(r, p)
      PROVE \A a \in ackMessages' : AckOriginRecord(a, retained', term', canonical')
    <2>1. AckOriginRecord(Ack(r, p.owner, p.epoch, p.first, Result(p)), retained', term', canonical')
        BY NewRecoveryAckOrigin, <1>1, <1>3, <1>7
    <2> QED BY SMT, <1>4, <1>7, <2>1 DEF AckProposal
<1> QED BY SMT, <1>4, <1>5, <1>6, <1>7 DEF AckOrigin, AckOriginRecord
=============================================================================
