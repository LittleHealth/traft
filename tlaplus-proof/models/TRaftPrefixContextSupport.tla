---------------------- MODULE TRaftPrefixContextSupport ----------------------
EXTENDS TRaftEntryContextProof, TRaftDurabilityProof, TRaftOfferProof

THEOREM PrefixContextStepFacts ==
    (Inv /\ ProofNext /\ RecoveryInvariant') =>
       /\ EntryContextUnique'
       /\ entryContexts \subseteq entryContexts'
       /\ commitHistory \subseteq commitHistory'
<1>1. ASSUME Inv, ProofNext, RecoveryInvariant'
      PROVE EntryContextUnique' /\ entryContexts \subseteq entryContexts'
            /\ commitHistory \subseteq commitHistory'
    <2>1. CommitEvidenceSound'
        BY EvidenceInductiveStep, <1>1
           DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant, ProofNext
    <2>2. EntryContextUnique'
        BY ExactEntryContextsInductiveStep, <1>1, <2>1
    <2> QED BY SMT, <1>1, <2>2 DEF ProofNext, Next, Observe
<1> QED BY <1>1

THEOREM KnownBySurvivesHistoryGrowth ==
    ASSUME NEW H, NEW J, H \subseteq J, NEW t, NEW e, KnownBy(H, t, e)
    PROVE KnownBy(J, t, e)
BY SMT DEF KnownBy

THEOREM OldOfferHasContext ==
    ASSUME ProofInvariant, NEW o \in offers
    PROVE \E ctx \in entryContexts : ctx.entry = o.entry
<1>1. PICK v \in leaderViews : v.epoch = o.epoch /\ o.entry \in v.entries
    BY SMT DEF ProofInvariant, OfferProvenance
<1>2. v.epoch \in Terms /\ o.entry \in canonical[v.epoch]
    BY SMT, <1>1 DEF ProofInvariant, CanonicalViewLinks
<1>3. ContextSound(canonical[v.epoch])
    BY <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>2, <1>3 DEF ContextSound

THEOREM OldAcknowledgedEntryHasContext ==
    ASSUME ProofInvariant, NEW a \in ackMessages, NEW e \in a.contents
    PROVE \E ctx \in entryContexts : ctx.entry = e
<1>1. a.epoch \in Terms /\ e \in canonical[a.epoch]
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin
<1>2. ContextSound(canonical[a.epoch])
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>1, <1>2 DEF ContextSound

THEOREM OldAndNewContextsAgree ==
    ASSUME EntryContextUnique', entryContexts \subseteq entryContexts',
           NEW old \in entryContexts, NEW fresh \in entryContexts', old.entry = fresh.entry
    PROVE old.prefix = fresh.prefix
BY SMT DEF EntryContextUnique
=============================================================================
