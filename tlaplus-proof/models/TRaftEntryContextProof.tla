------------------------ MODULE TRaftEntryContextProof -----------------------
EXTENDS TRaftInvariantDefinitions, TRaftCanonicalPrefixProof,
        TRaftContextOriginProof, TRaftCommitSupport

ExactContexts(C, E) == \A ctx \in E : ctx.entry.term \in Terms
    /\ ctx.prefix = Prefix(C[ctx.entry.term], ctx.entry.part - 1)

THEOREM CandidateContextsAreExact ==
    (ProofInvariant /\ EntryContextUnique) => ExactContexts(canonical, entryContexts)
<1>1. ASSUME ProofInvariant, EntryContextUnique, NEW ctx \in entryContexts
      PROVE ctx.entry.term \in Terms
            /\ ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
    <2>1. ctx.entry.term \in Terms
        BY <1>1 DEF ProofInvariant, ContextOrigins
    <2>2. ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
        BY ContextOriginIdentifiesCanonicalPrefix, <1>1
           DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1 DEF ExactContexts

THEOREM ExactContextsSurviveCanonicalGrowth ==
    ASSUME ExactContexts(canonical, entryContexts), ContextOrigins(canonical, entryContexts),
           CanonicalPrefixesPersist(canonical, canonical')
    PROVE ExactContexts(canonical', entryContexts)
BY SMT DEF ExactContexts, ContextOrigins, CanonicalPrefixesPersist

THEOREM ObservedPostContextsAreExact ==
    ASSUME ExactContexts(canonical', entryContexts), RecoveryInvariant', Observe
    PROVE ExactContexts(canonical', entryContexts')
<1>1. \A r \in Replicas : term'[r] \in Terms
          /\ (role'[r] = "Leader" => formal'[r] = canonical'[term'[r]])
    BY DEF RecoveryInvariant, TypeOK, CanonicalShape
<1>2. \A p \in proposals' : p.first.term = p.epoch /\ p.epoch \in Terms
          /\ p.prefix = Prefix(canonical'[p.epoch], p.first.part - 1)
    BY SMT DEF RecoveryInvariant, TypeOK, CanonicalShape
<1>3. \A r \in Replicas : role'[r] = "Leader" =>
          \A e \in formal'[r] : e.term = term'[r] =>
              e.term \in Terms /\ Prefix(formal'[r], e.part - 1) = Prefix(canonical'[e.term], e.part - 1)
    BY ONLY SMT, <1>1
<1> QED BY SMT, <1>2, <1>3 DEF ExactContexts, Observe

THEOREM RecoveryEvidenceHasContexts ==
    (RecoveryInvariant /\ CommitEvidenceSound) =>
        \A f \in commitHistory : \E ctx \in entryContexts : ctx.entry = f.entry
<1>1. ASSUME RecoveryInvariant, CommitEvidenceSound, NEW f \in commitHistory
      PROVE \E ctx \in entryContexts : ctx.entry = f.entry
    <2>1. f \in Evidence(ackMessages)
        BY <1>1 DEF CommitEvidenceSound
    <2>2. PICK c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
        BY IndependentEvidenceHasActualDistinctSenders, <2>1
    <2>3. MessageAckers(ackMessages, c, f.epoch, f.entry) # {}
        BY QuorumIsNonempty, <2>2
    <2>4. PICK a \in ackMessages : a.epoch = f.epoch /\ f.entry \in a.contents
        BY SMT, <2>3 DEF MessageAckers
    <2>5. a.epoch \in Terms /\ a.contents \subseteq canonical[a.epoch]
        BY <1>1, <2>4 DEF RecoveryInvariant, AckOrigin
    <2>6. ContextSound(canonical[a.epoch])
        BY <1>1, <2>5 DEF RecoveryInvariant, CanonicalShape
    <2> QED BY SMT, <2>4, <2>5, <2>6 DEF ContextSound
<1> QED BY <1>1

THEOREM ExactEntryContextsInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant', CommitEvidenceSound'
    PROVE EntryContextUnique'
<1>1. ProofInvariant /\ EntryContextUnique /\ ElectionSafety
      /\ ContextOrigins(canonical, entryContexts)
    BY DEF Inv, Safety, ProofInvariant
<1>2. term' \in [Replicas -> Terms]
    BY DEF RecoveryInvariant, TypeOK
<1>3. CanonicalPrefixesPersist(canonical, canonical')
    BY CanonicalPrefixesInductiveStep, <1>1, <1>2
<1>4. ExactContexts(canonical, entryContexts)
    BY CandidateContextsAreExact, <1>1
<1>5. ExactContexts(canonical', entryContexts)
    BY ExactContextsSurviveCanonicalGrowth, <1>1, <1>3, <1>4
<1>6. ExactContexts(canonical', entryContexts')
    BY ObservedPostContextsAreExact, <1>5 DEF ProofNext, Next
<1>7. \A a, b \in entryContexts' : a.entry = b.entry => a.prefix = b.prefix
    BY ONLY SMT, <1>6 DEF ExactContexts
<1>8. RecoveryEvidenceHasContexts'
    BY ONLY PTL, RecoveryEvidenceHasContexts
<1>9. \A f \in commitHistory' : \E ctx \in entryContexts' : ctx.entry = f.entry
    BY <1>8
<1> QED BY ONLY <1>7, <1>9 DEF EntryContextUnique
=============================================================================
