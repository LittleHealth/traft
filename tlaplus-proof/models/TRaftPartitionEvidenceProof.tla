---------------------- MODULE TRaftPartitionEvidenceProof ---------------------
EXTENDS TRaftAgreementFromInvariant, TRaftRecoveryContextProof

THEOREM TwoEvidenceEntriesHaveCommonCanonical ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW a \in commitHistory, NEW b \in commitHistory
    PROVE \E t \in Terms : a.entry \in canonical[t] /\ b.entry \in canonical[t]
<1>1. a.epoch \in Terms /\ b.epoch \in Terms /\ a.epoch \in Nat /\ b.epoch \in Nat
    BY SMT, EvidenceIsPossible DEF Terms
<1>2. a.entry \in canonical[a.epoch] /\ b.entry \in canonical[b.epoch]
    BY EvidenceHasCanonicalSource
<1>3. CASE a.epoch = b.epoch
    BY <1>1, <1>2, <1>3
<1>4. CASE a.epoch < b.epoch
    <2>1. a.entry \in canonical[b.epoch]
        BY EarlierEvidenceBelongsToLaterCanonical, <1>1, <1>2, <1>4
    <2> QED BY <1>1, <1>2, <2>1
<1>5. CASE b.epoch < a.epoch
    <2>1. b.entry \in canonical[a.epoch]
        BY EarlierEvidenceBelongsToLaterCanonical, <1>1, <1>2, <1>5
    <2> QED BY <1>1, <1>2, <2>1
<1> QED BY SMT, <1>1, <1>3, <1>4, <1>5

THEOREM EvidencePartitionOriginsAgree ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW a \in commitHistory, NEW b \in commitHistory,
           a.entry.part = b.entry.part
    PROVE a.entry.term = b.entry.term
<1>1. PICK t \in Terms : a.entry \in canonical[t] /\ b.entry \in canonical[t]
    BY TwoEvidenceEntriesHaveCommonCanonical
<1>2. Coherent(canonical[t])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>1, <1>2 DEF Coherent

THEOREM EvidenceEntryBelongsToCreationCanonical ==
    ASSUME ProofInvariant, EntryContextUnique, NEW f \in commitHistory
    PROVE f.entry.term \in Terms /\ f.entry \in canonical[f.entry.term]
<1>1. PICK ctx \in entryContexts : ctx.entry = f.entry
    BY DEF EntryContextUnique
<1> QED BY <1>1 DEF ProofInvariant, ContextOrigins

THEOREM ContextPartitionIsCanonical ==
    ASSUME ProofInvariant, EntryContextUnique, NEW t \in Terms,
           NEW ctx \in entryContexts, ctx.entry \in canonical[t],
           NEW p \in Int, p < ctx.entry.part
    PROVE Part(ctx.prefix, p) = Part(canonical[t], p)
<1>1. ContextSound(canonical[t]) /\ ctx.entry \in Entries
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>2. PICK source \in entryContexts : source.entry = ctx.entry
          /\ source.prefix = Prefix(canonical[t], ctx.entry.part - 1)
    BY SMT, <1>1 DEF ContextSound
<1>3. ctx.prefix = Prefix(canonical[t], ctx.entry.part - 1)
    BY SMT, <1>2 DEF EntryContextUnique
<1> QED BY SMT, <1>1, <1>3 DEF Part, Prefix, Entries, Partitions

THEOREM CommittedBoundaryClosesPartition ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           NEW boundary \in commitHistory, NEW ctx \in entryContexts, ctx.entry = boundary.entry,
           NEW p \in Int, p < ctx.entry.part, NEW f \in commitHistory, f.entry.part = p
    PROVE f.entry \in Part(ctx.prefix, p)
<1>1. PICK t \in Terms : boundary.entry \in canonical[t] /\ f.entry \in canonical[t]
    BY TwoEvidenceEntriesHaveCommonCanonical
<1>2. Part(ctx.prefix, p) = Part(canonical[t], p)
    BY ContextPartitionIsCanonical, <1>1
<1> QED BY SMT, <1>1, <1>2 DEF Part

THEOREM CanonicalRecoveryExtensionHasCurrentOrigin ==
    ASSUME ProofInvariant, NEW p \in proposals, NEW e \in canonical[p.epoch], e.part >= p.first.part
    PROVE e.term = p.epoch
<1>1. p.epoch \in Terms /\ p.first.term = p.epoch /\ p.first.part = Cur(p.prefix) + 1
      /\ p.prefix \subseteq Entries /\ IsFiniteSet(Result(p)) /\ e \in Entries
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       CanonicalShape, FiniteLogInvariant, FiniteProposals
<1>2. p.prefix \subseteq Result(p)
    BY SMT DEF Result
<1>3. IsFiniteSet(p.prefix)
    BY ONLY ZenonT(5), FS_Subset, <1>1, <1>2
<1>4. Cur(p.prefix) \in Int /\ \A x \in p.prefix : x.part \in Int /\ x.part <= Cur(p.prefix)
    BY FiniteLogPartitionFrontier, <1>1, <1>3
<1>5. e \notin p.prefix
    BY SMT, <1>1, <1>4 DEF Entries, Partitions
<1>6. \A x \in canonical[p.epoch] \ Result(p) : x.term = p.epoch
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>1, <1>5, <1>6 DEF Result
=============================================================================
