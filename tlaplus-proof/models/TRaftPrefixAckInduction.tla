------------------------ MODULE TRaftPrefixAckInduction -----------------------
EXTENDS TRaftPrefixContextSupport, TRaftAckSourceFrames, TRaftRecoveryContextProof

THEOREM AckPrefixEvidenceUnion ==
    ASSUME NEW A, NEW B, NEW E, NEW H, AckPrefixEvidence(A, E, H), AckPrefixEvidence(B, E, H)
    PROVE AckPrefixEvidence(A \cup B, E, H)
BY SMT DEF AckPrefixEvidence

THEOREM OldAcknowledgementsKeepPrefixEvidence ==
    ASSUME ProofInvariant, EntryContextUnique', entryContexts \subseteq entryContexts',
           commitHistory \subseteq commitHistory'
    PROVE AckPrefixEvidence(ackMessages, entryContexts', commitHistory')
<1>1. ASSUME NEW a \in ackMessages, NEW ctx \in entryContexts', ctx.entry \in a.contents,
            a.sender # a.receiver \/ a.contents # {a.target}
      PROVE \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory', a.epoch, x)
    <2>1. PICK old \in entryContexts : old.entry = ctx.entry
        BY OldAcknowledgedEntryHasContext, <1>1
    <2>2. old.prefix = ctx.prefix
        BY OldAndNewContextsAgree, <1>1, <2>1
    <2>3. \A x \in old.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
        BY <1>1, <2>1 DEF ProofInvariant, PrefixEvidenceInvariant, AckPrefixEvidence
    <2> QED BY SMT, KnownBySurvivesHistoryGrowth, <2>2, <2>3
<1> QED BY <1>1 DEF AckPrefixEvidence

THEOREM NewEntryAcknowledgementHasPrefixEvidence ==
    ASSUME ProofInvariant, RecoveryInvariant', EntryContextUnique',
           entryContexts \subseteq entryContexts', commitHistory \subseteq commitHistory',
           NEW r \in Replicas, NEW o, AckEntry(r, o)
    PROVE AckPrefixEvidence({Ack(r, o.owner, o.epoch, o.entry, {o.entry})}, entryContexts', commitHistory')
<1>1. o.entry \in formal[r] /\ o.epoch = term[r]
      /\ UNCHANGED retained
      /\ Ack(r, o.owner, o.epoch, o.entry, {o.entry}) \in ackMessages'
    BY SMT DEF AckEntry
<1>2. ContextSound(formal[r]) /\ FollowerPrefixEvidence(formal, term, retained, commitHistory)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, PrefixEvidenceInvariant
<1>3. PICK p \in retained[r] : p.epoch = o.epoch /\ p.owner = o.owner
    BY SMT, <1>1 DEF RecoveryInvariant, AckOrigin, Ack
<1>4. PICK old \in entryContexts : old.entry = o.entry
          /\ old.prefix = Prefix(formal[r], o.entry.part - 1)
    BY SMT, <1>1, <1>2 DEF ContextSound
<1>5. o.entry.term = o.epoch
    BY SMT DEF AckEntry, ProofInvariant, OfferProvenance
<1>6. ASSUME NEW ctx \in entryContexts', ctx.entry = o.entry, r # o.owner
      PROVE \A x \in ctx.prefix : KnownBy(commitHistory', o.epoch, x)
    <2>1. ctx.prefix = Prefix(formal[r], o.entry.part - 1)
        BY OldAndNewContextsAgree, <1>4, <1>6
    <2>2. \A x \in ctx.prefix : KnownBy(commitHistory, o.epoch, x)
        BY ONLY SMT, <1>1, <1>2, <1>3, <1>5, <1>6, <2>1 DEF FollowerPrefixEvidence
    <2> QED BY KnownBySurvivesHistoryGrowth, <2>2
<1> QED BY SMT, <1>6 DEF AckPrefixEvidence, Ack

THEOREM ProposalEntryHasOldContext ==
    ASSUME ProofInvariant, NEW p \in proposals, NEW e \in Result(p)
    PROVE \E ctx \in entryContexts : ctx.entry = e
<1>1. p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
      /\ ContextSound(canonical[p.epoch])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1> QED BY SMT, <1>1 DEF ContextSound

THEOREM NewProposalAcknowledgementHasPrefixEvidence ==
    ASSUME ProofInvariant, EntryContextUnique, EntryContextUnique',
           entryContexts \subseteq entryContexts', NEW r \in Replicas, NEW p, AckProposal(r, p)
    PROVE AckPrefixEvidence({Ack(r, p.owner, p.epoch, p.first, Result(p))}, entryContexts', commitHistory')
<1>1. p \in proposals
    BY SMT DEF AckProposal, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. ASSUME NEW ctx \in entryContexts', ctx.entry \in Result(p)
      PROVE ctx.prefix \subseteq Result(p)
    <2>1. PICK old \in entryContexts : old.entry = ctx.entry
        BY ProposalEntryHasOldContext, <1>1, <1>2
    <2>2. ctx.prefix = old.prefix
        BY OldAndNewContextsAgree, <1>2, <2>1
    <2>3. old.prefix \subseteq Result(p)
        BY RecoveryResultContainsEntryContext, <1>1, <1>2, <2>1
    <2> QED BY <2>2, <2>3
<1> QED BY SMT, <1>2 DEF AckPrefixEvidence, Ack

THEOREM AckPrefixEvidenceInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant'
    PROVE AckPrefixEvidence(ackMessages', entryContexts', commitHistory')
<1>1. ProofInvariant /\ ProtocolNext /\ EntryContextUnique /\ EntryContextUnique'
      /\ entryContexts \subseteq entryContexts' /\ commitHistory \subseteq commitHistory'
    BY PrefixContextStepFacts DEF Inv, Safety, ProofNext, Next
<1>2. AckPrefixEvidence(ackMessages, entryContexts', commitHistory')
    BY OldAcknowledgementsKeepPrefixEvidence, <1>1
<1>3. (\E r \in Replicas : \E o : AckEntry(r, o))
          \/ (\E r \in Replicas : \E p : AckProposal(r, p)) \/ UNCHANGED ackMessages
    BY OnlyAckActionsChangeMessages, <1>1
<1>4. ASSUME NEW r \in Replicas, NEW o, AckEntry(r, o)
      PROVE AckPrefixEvidence(ackMessages', entryContexts', commitHistory')
    <2>1. AckPrefixEvidence({Ack(r, o.owner, o.epoch, o.entry, {o.entry})}, entryContexts', commitHistory')
        BY NewEntryAcknowledgementHasPrefixEvidence, <1>1, <1>4
    <2>2. ackMessages' = ackMessages \cup {Ack(r, o.owner, o.epoch, o.entry, {o.entry})}
        BY <1>4 DEF AckEntry
    <2> QED BY ONLY AckPrefixEvidenceUnion, <1>2, <2>1, <2>2
<1>5. ASSUME NEW r \in Replicas, NEW p, AckProposal(r, p)
      PROVE AckPrefixEvidence(ackMessages', entryContexts', commitHistory')
    <2>1. AckPrefixEvidence({Ack(r, p.owner, p.epoch, p.first, Result(p))}, entryContexts', commitHistory')
        BY NewProposalAcknowledgementHasPrefixEvidence, <1>1, <1>5
    <2>2. ackMessages' = ackMessages \cup {Ack(r, p.owner, p.epoch, p.first, Result(p))}
        BY <1>5 DEF AckProposal
    <2> QED BY ONLY AckPrefixEvidenceUnion, <1>2, <2>1, <2>2
<1> QED BY SMT, <1>2, <1>3, <1>4, <1>5
=============================================================================
