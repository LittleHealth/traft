---------------------- MODULE TRaftAppliedEvidencePrefix ---------------------
EXTENDS TRaftApplicationPrefixProof, TRaftPartitionEvidenceProof

AppliedEvidencePrefixClosed == \A r \in Replicas : \A e \in applied[r] :
    Prefix(EvidenceEntries, e.part - 1) \subseteq applied[r]

THEOREM AppliedBoundaryContainsEarlierEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           AppliedEntriesPreserved, AppliedPrefixClosure,
           NEW r \in Replicas, NEW e \in applied[r], NEW f \in commitHistory,
           f.entry.part < e.part
    PROVE f.entry \in applied[r]
<1>1. e \in formal[r] /\ ContextSound(formal[r])
      /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]
    BY DEF AppliedEntriesPreserved, AppliedPrefixClosure, PrefixClosed,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>2. PICK boundary \in commitHistory : boundary.entry = e
    BY DEF ProofInvariant, HistoryOriginInvariant, AppliedEvidence
<1>3. PICK ctx \in entryContexts : ctx.entry = e /\ ctx.prefix = Prefix(formal[r], e.part - 1)
    BY <1>1 DEF ContextSound
<1>4. f.entry.term \in Terms /\ f.entry \in canonical[f.entry.term]
    BY EvidenceEntryBelongsToCreationCanonical
<1>5. f.entry.part \in Int
    BY <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       CanonicalShape, Entries, Partitions
<1>6. f.entry \in Part(ctx.prefix, f.entry.part)
    BY CommittedBoundaryClosesPartition, <1>2, <1>3, <1>5
<1> QED BY SMT, <1>1, <1>3, <1>6 DEF Part

THEOREM ApplicationPrefixesContainAllEarlierEvidence ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique
     /\ AppliedEntriesPreserved /\ AppliedPrefixClosure) => AppliedEvidencePrefixClosed
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
            AppliedEntriesPreserved, AppliedPrefixClosure, NEW r \in Replicas,
            NEW e \in applied[r], NEW x \in Prefix(EvidenceEntries, e.part - 1)
      PROVE x \in applied[r]
    <2>1. PICK f \in commitHistory : f.entry = x
        BY <1>1 DEF Prefix, EvidenceEntries
    <2>2. x.part <= e.part - 1 /\ x.part \in Int /\ e.part \in Int
        <3>1. x.part <= e.part - 1
            BY ONLY <1>1 DEF Prefix
        <3>2. f.entry.term \in Terms /\ f.entry \in canonical[f.entry.term]
            BY EvidenceEntryBelongsToCreationCanonical, <1>1, <2>1
        <3>3. canonical \in [Terms -> SUBSET Entries]
              /\ applied \in [Replicas -> SUBSET Entries]
            BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
                CanonicalShape, TypeOK
        <3>4. x \in Entries /\ e \in Entries
            BY ONLY SMT, <1>1, <2>1, <3>2, <3>3
        <3> QED BY ONLY SMT, <3>1, <3>4 DEF Entries, Partitions
    <2>3. f.entry.part < e.part
        BY ONLY SMT, <2>1, <2>2
    <2> QED BY AppliedBoundaryContainsEarlierEvidence, <1>1, <2>1, <2>3
<1> QED BY <1>1 DEF AppliedEvidencePrefixClosed

THEOREM AppliedBoundaryPrefixEqualsEvidencePrefix ==
    ASSUME AppliedEvidencePrefixClosed, AppliedEvidence,
           NEW r \in Replicas, NEW e \in applied[r]
    PROVE Prefix(applied[r], e.part - 1) = Prefix(EvidenceEntries, e.part - 1)
BY SMT DEF AppliedEvidencePrefixClosed, AppliedEvidence, EvidenceEntries, Prefix
=============================================================================
