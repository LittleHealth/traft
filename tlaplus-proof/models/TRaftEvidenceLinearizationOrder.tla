------------------ MODULE TRaftEvidenceLinearizationOrder --------------------
EXTENDS TRaftPartitionEvidenceProof, TRaftInvariantDefinitions

THEOREM CertifiedContextCapturesLowerEvidence ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique) =>
      \A ctx \in entryContexts :
        (\E boundary \in commitHistory : boundary.entry = ctx.entry) =>
          Prefix(EvidenceEntries, ctx.entry.part - 1) \subseteq ctx.prefix
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
            NEW ctx \in entryContexts, NEW boundary \in commitHistory,
            boundary.entry = ctx.entry,
            NEW x \in Prefix(EvidenceEntries, ctx.entry.part - 1)
      PROVE x \in ctx.prefix
    <2>1. PICK f \in commitHistory : f.entry = x
        BY <1>1 DEF Prefix, EvidenceEntries
    <2>2. x.part \in Int /\ ctx.entry.part \in Int /\ x.part <= ctx.entry.part - 1
        BY SMT, EvidenceEntryBelongsToCreationCanonical, <1>1, <2>1
           DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
               CanonicalShape, Entries, Partitions, Prefix
    <2>3. f.entry.part < ctx.entry.part
        BY ONLY SMT, <2>1, <2>2
    <2>4. f.entry \in Part(ctx.prefix, f.entry.part)
        BY CommittedBoundaryClosesPartition, <1>1, <2>1, <2>2, <2>3
    <2> QED BY SMT, <2>1, <2>4 DEF Part
<1> QED BY <1>1

THEOREM CertifiedContextAlreadyHasAllPrefixEvidence ==
    ASSUME EvidenceRespectsPartitionOrder, NEW ctx \in entryContexts,
           NEW f \in commitHistory, ctx.entry = f.entry
    PROVE ctx.prefix \subseteq EvidenceEntries
BY SMT DEF EvidenceRespectsPartitionOrder, EvidenceEntries

\* This compares consecutive observable states, not authorization epochs.
\* New evidence cannot fill an older partition after a later partition has
\* already acquired evidence. No protocol action consults this predicate.
NewEvidenceFollowsOldPartitions == \A e \in EvidenceEntries' \ EvidenceEntries :
    \A old \in EvidenceEntries : old.part <= e.part

THEOREM FirstEvidenceFormationRespectsPartitionOrder ==
    ASSUME Inv, Next, Inv'
    PROVE NewEvidenceFollowsOldPartitions
<1>1. entryContexts \subseteq entryContexts' /\ commitHistory \subseteq commitHistory'
      /\ ProofInvariant /\ ProofInvariant' /\ EntryContextUnique /\ EntryContextUnique'
      /\ CommitEvidenceSound' /\ EvidenceRespectsPartitionOrder
    BY DEF Inv, Safety, Next, Observe
<1>2. CertifiedContextCapturesLowerEvidence'
    BY ONLY PTL, CertifiedContextCapturesLowerEvidence
<1>3. \A ctx \in entryContexts' :
          (\E boundary \in commitHistory' : boundary.entry = ctx.entry) =>
            Prefix(EvidenceEntries', ctx.entry.part - 1) \subseteq ctx.prefix
    BY <1>1, <1>2
<1>4. ASSUME NEW e \in EvidenceEntries' \ EvidenceEntries, NEW old \in EvidenceEntries
      PROVE old.part <= e.part
    <2>1. PICK boundary \in commitHistory : boundary.entry = old
        BY <1>4 DEF EvidenceEntries
    <2>2. PICK ctx \in entryContexts : ctx.entry = old
        BY <1>1, <2>1 DEF EntryContextUnique
    <2>3. ctx.prefix \subseteq EvidenceEntries
        BY CertifiedContextAlreadyHasAllPrefixEvidence, <1>1, <2>1, <2>2
    <2>4. Prefix(EvidenceEntries', old.part - 1) \subseteq ctx.prefix
        BY <1>1, <1>3, <2>1, <2>2
    <2>5. old.part \in Int /\ e.part \in Int
        BY SMT, <1>1, <1>4, <2>2
           DEF ProofInvariant, ContextOrigins, PreProvenanceInvariant, RecoveryInvariant,
               CanonicalShape, Entries, Partitions, EvidenceEntries, EntryContextUnique
    <2> QED BY ONLY SMT, <1>4, <2>3, <2>4, <2>5 DEF Prefix
<1> QED BY <1>4 DEF NewEvidenceFollowsOldPartitions

THEOREM EvidenceIndexOrderRespectsPartitions ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW a \in EvidenceEntries,
           NEW b \in EvidenceEntries, a.index < b.index
    PROVE a.part <= b.part
<1>1. PICK fa \in commitHistory : fa.entry = a
    BY DEF EvidenceEntries
<1>2. PICK fb \in commitHistory : fb.entry = b
    BY DEF EvidenceEntries
<1>3. PICK t \in Terms : a \in canonical[t] /\ b \in canonical[t]
    BY TwoEvidenceEntriesHaveCommonCanonical, <1>1, <1>2
<1>4. Coherent(canonical[t])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY <1>3, <1>4 DEF Coherent
=============================================================================
