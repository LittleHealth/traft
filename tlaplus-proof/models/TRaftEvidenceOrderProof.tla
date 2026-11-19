------------------------ MODULE TRaftEvidenceOrderProof ----------------------
EXTENDS TRaftRecoveryContextProof, TRaftProposalEvidenceProof
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM QuorumContainsOtherReplica ==
    ASSUME NEW Q, Quorum(Q), NEW c
    PROVE \E r \in Q : r # c
<1>1. IsFiniteSet(Q) /\ Cardinality(Q) \in Nat /\ Cardinality(Replicas) \in Nat
    BY SMT, FS_Subset, FS_CardinalityType DEF Quorum
<1>2. IsFiniteSet({c}) /\ Cardinality({c}) = 1
    BY FS_Singleton
<1>3. ASSUME Q \subseteq {c}
      PROVE FALSE
    <2>0. Q \subseteq {c}
        BY <1>3
    <2>1. Cardinality(Q) <= 1
        BY ONLY SMT, FS_Subset, <2>0, <1>1, <1>2
    <2> QED BY SMT, <1>1, <2>1 DEF Quorum
<1> QED BY SMT, <1>3

RecoveryFirst(e, t) == \E p \in proposals : p.epoch = t /\ p.first = e

THEOREM CurrentExtensionAcknowledgementIsSingleton ==
    ASSUME ProofInvariant, NEW a \in ackMessages, NEW e \in a.contents,
           e.term = a.epoch, ~RecoveryFirst(e, a.epoch)
    PROVE a.contents = {e} /\ a.target = e
<1>00. a \in ackMessages /\ e \in a.contents /\ e.term = a.epoch
      /\ ~RecoveryFirst(e, a.epoch)
    OBVIOUS
<1>0. AckHasSource(a, proposals, offers)
      /\ (\A p \in proposals : p.epoch \in Nat /\ (\A x \in p.prefix : x.term \in Nat /\ x.term < p.epoch))
    BY DEF ProofInvariant, MessageSourceInvariant, AckSourceInvariant,
       PrefixEvidenceInvariant, RecoveryProposalBoundaries, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Entries, Terms
<1>1. ASSUME NEW p \in proposals,
             a = Ack(a.sender, p.owner, p.epoch, p.first, Result(p))
      PROVE FALSE
    <2>1. a.epoch = p.epoch /\ a.contents = p.prefix \cup {p.first}
        BY <1>1 DEF Ack, Result
    <2>2. e \notin p.prefix
        BY ONLY SMT, <1>00, <1>0, <1>1, <2>1
    <2> QED BY SMT, <1>00, <1>1, <2>1, <2>2 DEF RecoveryFirst
<1>2. PICK o \in offers : a = Ack(a.sender, o.owner, o.epoch, o.entry, {o.entry})
    BY ONLY SMT, <1>0, <1>1 DEF AckHasSource
<1> QED BY ONLY SMT, <1>00, <1>2 DEF Ack

THEOREM RecoveryFirstAcknowledgementCoversContext ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           NEW a \in ackMessages, NEW ctx \in entryContexts,
           ctx.entry \in a.contents, RecoveryFirst(ctx.entry, a.epoch)
    PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
<1>00. ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique
      /\ a \in ackMessages /\ ctx \in entryContexts /\ ctx.entry \in a.contents
    OBVIOUS
<1>0. AckHasSource(a, proposals, offers)
      /\ confirmations \subseteq proposals
      /\ (\A p, q \in proposals : p.epoch = q.epoch => p = q)
      /\ (\A p \in proposals : p.epoch \in Terms \ {0})
    BY DEF ProofInvariant, MessageSourceInvariant, AckSourceInvariant, ConfirmationSources,
       PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>1. ASSUME NEW p \in proposals,
             a = Ack(a.sender, p.owner, p.epoch, p.first, Result(p))
      PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
    <2>1. a.contents = Result(p) /\ ctx.entry \in Result(p)
        BY SMT, <1>1 DEF Ack
    <2>2. ctx.prefix \subseteq Result(p)
        BY RecoveryResultContainsEntryContext, <1>1, <2>1
    <2> QED BY ONLY SMT, <2>1, <2>2
<1>2. ASSUME NEW o \in offers,
             a = Ack(a.sender, o.owner, o.epoch, o.entry, {o.entry})
      PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
    <2>1. a.epoch = o.epoch /\ ctx.entry = o.entry
        BY SMT, <1>2 DEF Ack
    <2>2. PICK v \in leaderViews : v.epoch = o.epoch
        BY SMT, <1>2 DEF ProofInvariant, OfferProvenance
    <2>3. PICK q \in confirmations : q.epoch = v.epoch
        BY <2>2 DEF ProofInvariant, PrefixEvidenceInvariant, ActiveRecoveryCertificates, LeaderViewsCertified
    <2>4. PICK p \in proposals : p.epoch = a.epoch /\ p.first = ctx.entry
        BY DEF RecoveryFirst
    <2>5. q \in proposals /\ q = p /\ q.epoch = a.epoch /\ ctx.entry = q.first
          /\ a.epoch \in Nat
        BY ONLY SMT, <1>0, <2>1, <2>2, <2>3, <2>4 DEF Terms
    <2>6. ctx.entry \in Result(q)
        BY ONLY <2>5 DEF Result
    <2>7. ctx.prefix \subseteq Result(q)
        BY RecoveryResultContainsEntryContext, <2>5, <2>6
    <2>8. Quorum(ProposalSenders(ackMessages, q))
        BY <2>3 DEF ProofInvariant, KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders
    <2>9. \A x \in ctx.prefix : [epoch |-> a.epoch, entry |-> x] \in commitHistory
        BY ONLY ChosenProposalHasEntryEvidence, <1>00, <2>5, <2>7, <2>8
    <2>10. \A x \in ctx.prefix : KnownBy(commitHistory, a.epoch, x)
        BY ONLY EvidenceRecordIsKnown, <2>5, <2>9
    <2> QED BY <2>10
<1> QED BY ONLY ZenonT(5), <1>0, <1>1, <1>2 DEF AckHasSource

THEOREM OlderOrRecoveryFirstAcknowledgementCoversContext ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique, NEW a \in ackMessages,
           NEW ctx \in entryContexts, ctx.entry \in a.contents,
           ~(ctx.entry.term = a.epoch /\ ~RecoveryFirst(ctx.entry, a.epoch))
    PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
<1>0. AckHasSource(a, proposals, offers)
      /\ (\A o \in offers : o.entry.term = o.epoch)
    BY DEF ProofInvariant, MessageSourceInvariant, AckSourceInvariant, OfferProvenance
<1>1. ASSUME NEW p \in proposals,
             a = Ack(a.sender, p.owner, p.epoch, p.first, Result(p))
      PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
    <2>1. a.contents = Result(p) /\ ctx.entry \in Result(p)
        BY SMT, <1>1 DEF Ack
    <2>2. ctx.prefix \subseteq Result(p)
        BY RecoveryResultContainsEntryContext, <1>1, <2>1
    <2> QED BY ONLY SMT, <2>1, <2>2
<1>2. ASSUME NEW o \in offers,
             a = Ack(a.sender, o.owner, o.epoch, o.entry, {o.entry})
      PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
    <2>1. ctx.entry.term = a.epoch
        BY SMT, <1>0, <1>2 DEF Ack
    <2>2. RecoveryFirst(ctx.entry, a.epoch)
        BY <2>1
    <2> QED BY RecoveryFirstAcknowledgementCoversContext, <2>2
<1> QED BY ONLY ZenonT(5), <1>0, <1>1, <1>2 DEF AckHasSource

THEOREM CurrentExtensionEvidenceHasPriorEvidence ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW t \in Terms \ {0},
           NEW ctx \in entryContexts, NEW x \in ctx.prefix,
           Quorum(MessageAckers(ackMessages, c, t, ctx.entry)),
           ctx.entry.term = t, ~RecoveryFirst(ctx.entry, t), x # ctx.entry
    PROVE KnownBy(commitHistory, t, x)
<1>1. PICK r \in MessageAckers(ackMessages, c, t, ctx.entry) : r # c
    BY QuorumContainsOtherReplica
<1>2. PICK a \in ackMessages : a.sender = r /\ a.receiver = c
          /\ a.epoch = t /\ ctx.entry \in a.contents
    BY SMT, <1>1 DEF MessageAckers
<1>3. a.contents = {ctx.entry}
    BY CurrentExtensionAcknowledgementIsSingleton, <1>2
<1>4. x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
    BY SMT, <1>1, <1>2 DEF ProofInvariant, PrefixEvidenceInvariant, AckPrefixEvidence
<1> QED BY SMT, <1>2, <1>3, <1>4

THEOREM RecoveryEvidenceHasPriorEvidence ==
    ASSUME ProofInvariant, EntryContextUnique, CommitEvidenceSound,
           NEW c \in Replicas, NEW t \in Terms \ {0},
           NEW ctx \in entryContexts, NEW x \in ctx.prefix,
           Quorum(MessageAckers(ackMessages, c, t, ctx.entry)),
           ~(ctx.entry.term = t /\ ~RecoveryFirst(ctx.entry, t))
    PROVE KnownBy(commitHistory, t, x)
<1>1. ASSUME ~KnownBy(commitHistory, t, x)
      PROVE FALSE
    <2>0. ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique /\ ctx \in entryContexts /\ x \in ctx.prefix
          /\ ~(ctx.entry.term = t /\ ~RecoveryFirst(ctx.entry, t)) /\ ~KnownBy(commitHistory, t, x)
        BY <1>1
    <2>1. \A a \in ackMessages :
              a.receiver = c /\ a.epoch = t /\ ctx.entry \in a.contents => x \in a.contents
        BY ONLY SMT, OlderOrRecoveryFirstAcknowledgementCoversContext, <2>0
    <2>2. MessageAckers(ackMessages, c, t, ctx.entry) \subseteq MessageAckers(ackMessages, c, t, x)
        BY SMT, <2>1 DEF MessageAckers
    <2>3. Quorum(MessageAckers(ackMessages, c, t, x))
        <3>1. IsFiniteSet(Replicas) /\ MessageAckers(ackMessages, c, t, x) \subseteq Replicas
            BY SMT DEF ParameterAssumptions, MessageAckers
        <3>2. Quorum(MessageAckers(ackMessages, c, t, ctx.entry))
            OBVIOUS
        <3> QED BY ONLY SMT, MajorityUpward, <2>2, <3>1, <3>2 DEF Majority, Quorum
    <2>4. [epoch |-> t, entry |-> x] \in commitHistory
        BY QuorumCreatesIndependentEvidence, <2>3 DEF CommitEvidenceSound
    <2>5. t \in Nat
        BY SMT DEF Terms
    <2> QED BY ONLY SMT, <2>0, <2>4, <2>5 DEF KnownBy
<1> QED BY <1>1

THEOREM CandidateImpliesEvidenceOrder ==
    (ProofInvariant /\ EntryContextUnique /\ CommitEvidenceSound) => EvidenceRespectsPartitionOrder
<1>1. ASSUME ProofInvariant, EntryContextUnique, CommitEvidenceSound,
            NEW f \in commitHistory, NEW ctx \in entryContexts, ctx.entry = f.entry,
            NEW x \in ctx.prefix
      PROVE KnownBy(commitHistory, f.epoch, x)
    <2>1. f \in Evidence(ackMessages) /\ f.epoch \in Terms \ {0}
        BY SMT, <1>1 DEF CommitEvidenceSound, Evidence
    <2>2. PICK c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
        BY IndependentEvidenceHasActualDistinctSenders, <2>1
    <2>3. ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
        BY ContextOriginIdentifiesCanonicalPrefix, <1>1
           DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>30. ContextOrigins(canonical, entryContexts) /\ canonical \in [Terms -> SUBSET Entries]
          /\ ctx \in entryContexts
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>4. ctx.entry \in Entries
        BY ONLY SMT, <1>1, <2>30 DEF ContextOrigins
    <2>5. x # ctx.entry
        BY SMT, <1>1, <2>3, <2>4 DEF Prefix, Entries, Partitions
    <2>6. CASE ctx.entry.term = f.epoch /\ ~RecoveryFirst(ctx.entry, f.epoch)
        BY CurrentExtensionEvidenceHasPriorEvidence, <1>1, <2>1, <2>2, <2>5, <2>6
    <2>7. CASE ~(ctx.entry.term = f.epoch /\ ~RecoveryFirst(ctx.entry, f.epoch))
        BY RecoveryEvidenceHasPriorEvidence, <1>1, <2>1, <2>2, <2>7
    <2> QED BY <2>6, <2>7
<1> QED BY SMT, <1>1 DEF EvidenceRespectsPartitionOrder, KnownBy
=============================================================================
