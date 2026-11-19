------------------------ MODULE TRaftPrefixOfferInduction ---------------------
EXTENDS TRaftPrefixContextSupport

THEOREM OldOfferCountsSurvive ==
    ASSUME ProofInvariant, EntryContextUnique', entryContexts \subseteq entryContexts',
           commitHistory \subseteq commitHistory'
    PROVE OfferCountEvidence(offers, entryContexts', commitHistory')
<1>1. ASSUME NEW o \in offers, NEW ctx \in entryContexts', ctx.entry = o.entry
      PROVE \E S \in SUBSET Part(ctx.prefix, o.entry.part - 1) :
              /\ IsFiniteSet(S) /\ Cardinality(S) = o.committed
              /\ \A x \in S : KnownBy(commitHistory', o.epoch, x)
    <2>1. PICK old \in entryContexts : old.entry = o.entry
        BY OldOfferHasContext, <1>1
    <2>2. old.prefix = ctx.prefix
        BY OldAndNewContextsAgree, <1>1, <2>1
    <2>3. PICK S \in SUBSET Part(old.prefix, o.entry.part - 1) :
              /\ IsFiniteSet(S) /\ Cardinality(S) = o.committed
              /\ \A x \in S : KnownBy(commitHistory, o.epoch, x)
        BY <1>1, <2>1 DEF ProofInvariant, PrefixEvidenceInvariant, OfferCountEvidence
    <2>4. \A x \in S : KnownBy(commitHistory', o.epoch, x)
        BY KnownBySurvivesHistoryGrowth, <2>3
    <2> QED BY <2>2, <2>3, <2>4
<1> QED BY <1>1 DEF OfferCountEvidence

THEOREM NewOfferCountHasEvidence ==
    ASSUME ProofInvariant, EntryContextUnique', entryContexts \subseteq entryContexts',
           commitHistory \subseteq commitHistory', NEW c \in Replicas, NEW e, SendEntry(c, e)
    PROVE OfferCountEvidence({NormalMessage(c, e)}, entryContexts', commitHistory')
<1>1. e \in formal[c] /\ ContextSound(formal[c]) /\ e \in Entries
      /\ IsFiniteSet(formal[c]) /\ term[c] \in Terms
    BY SMT DEF SendEntry, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData
<1>2. PICK old \in entryContexts : old.entry = e /\ old.prefix = Prefix(formal[c], e.part - 1)
    BY SMT, <1>1 DEF ContextSound
<1>3. DEFINE S == Part(formal[c] \cap knownCommitted[c], e.part - 1)
<1>4. S \subseteq formal[c] /\ IsFiniteSet(S)
    <2>1. S \subseteq formal[c]
        BY SMT DEF S, Part
    <2> QED BY FS_Subset, <1>1, <2>1
<1>5. \A x \in S : KnownBy(commitHistory', term[c], x)
    <2>1. \A x \in S : KnownBy(commitHistory, term[c], x)
        BY SMT DEF S, Part, ProofInvariant, PrefixEvidenceInvariant, EpochKnowledgeInvariant, KnowledgeAt
    <2> QED BY KnownBySurvivesHistoryGrowth, <2>1
<1>6. ASSUME NEW ctx \in entryContexts', ctx.entry = e
      PROVE \E W \in SUBSET Part(ctx.prefix, e.part - 1) :
          IsFiniteSet(W) /\ Cardinality(W) = NormalMessage(c, e).committed
          /\ \A x \in W : KnownBy(commitHistory', term[c], x)
    <2>1. ctx.prefix = Prefix(formal[c], e.part - 1)
        BY OldAndNewContextsAgree, <1>2, <1>6
    <2>2. e.part - 1 \in Int
        BY SMT, <1>1 DEF Entries, Partitions
    <2>3. S \subseteq Part(ctx.prefix, e.part - 1)
        BY ONLY SMT, <2>1, <2>2 DEF S, Part, Prefix
    <2>4. Cardinality(S) = NormalMessage(c, e).committed
        BY DEF S, NormalMessage, Count
    <2> QED BY <1>4, <1>5, <2>3, <2>4
<1> QED BY SMT, <1>6 DEF OfferCountEvidence, NormalMessage

THEOREM OfferPrefixEvidenceInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant'
    PROVE OfferCountEvidence(offers', entryContexts', commitHistory')
<1>1. ProofInvariant /\ ProtocolNext /\ EntryContextUnique'
      /\ entryContexts \subseteq entryContexts' /\ commitHistory \subseteq commitHistory'
    BY PrefixContextStepFacts DEF Inv, ProofNext, Next
<1>2. OfferCountEvidence(offers, entryContexts', commitHistory')
    BY OldOfferCountsSurvive, <1>1
<1>3. (\E c \in Replicas : \E e : SendEntry(c, e)) \/ UNCHANGED offers
    BY OnlySendEntryCreatesOffer, <1>1
<1>4. ASSUME NEW c \in Replicas, NEW e, SendEntry(c, e)
      PROVE OfferCountEvidence(offers', entryContexts', commitHistory')
    <2>1. OfferCountEvidence({NormalMessage(c, e)}, entryContexts', commitHistory')
        BY NewOfferCountHasEvidence, <1>1, <1>4
    <2> QED BY SMT, <1>2, <1>4, <2>1 DEF SendEntry, OfferCountEvidence
<1> QED BY SMT, <1>2, <1>3, <1>4
=============================================================================
