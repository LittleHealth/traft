----------------------- MODULE TRaftFollowerReceiveProof ----------------------
EXTENDS TRaftFollowerPrefixSupport

THEOREM FollowerKnowsBeforeOpenPartition ==
    ASSUME ProofInvariant, NEW r \in Replicas, Aligned(r, term[r]),
           NEW p \in retained[r], p.epoch = term[r], p.owner # r
    PROVE \A x \in Prefix(formal[r], Cur(formal[r]) - 1) : KnownBy(commitHistory, term[r], x)
<1>1. PICK e \in formal[r] : e.part = Cur(formal[r]) /\ e.term = term[r]
    BY AlignedOpenPartitionHasCurrentEntry
<1> QED BY <1>1 DEF ProofInvariant, PrefixEvidenceInvariant, FollowerPrefixEvidence

THEOREM BoundaryCountWitnessCoversPartition ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipBoundaryCommit,
           NEW r \in Replicas, NEW o \in offers, CanReceive(r, o),
           o.entry.part # Cur(formal[r])
    PROVE \A x \in Part(formal[r], Cur(formal[r])) : KnownBy(commitHistory, term[r], x)
<1>1. o.entry.part = Cur(formal[r]) + 1 /\ o.committed = o.entry.prevSize
      /\ o.entry.prevSize = Count(formal[r], Cur(formal[r])) /\ o.epoch = term[r]
    BY DEF CanReceive
<1>2. formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, FiniteLogInvariant, FiniteNodeData
<1>3. Cur(formal[r]) \in Int
    BY FiniteLogPartitionFrontier, <1>2
<1>4. PICK ctx \in entryContexts : ctx.entry = o.entry
    BY OldOfferHasContext
<1>5. Prefix(formal[r], o.entry.part - 1) = ctx.prefix
    BY NormalBoundaryUsesCompleteCommonPrefix, <1>4
<1>6. Part(ctx.prefix, o.entry.part - 1) = Part(formal[r], Cur(formal[r]))
    BY ONLY SMT, <1>1, <1>3, <1>5 DEF Prefix, Part
<1>7. PICK S \in SUBSET Part(ctx.prefix, o.entry.part - 1) :
          /\ IsFiniteSet(S) /\ Cardinality(S) = o.committed
          /\ \A x \in S : KnownBy(commitHistory, o.epoch, x)
    BY <1>4 DEF ProofInvariant, PrefixEvidenceInvariant, OfferCountEvidence
<1>8. IsFiniteSet(Part(formal[r], Cur(formal[r])))
    BY FinitePartitionCount, <1>2
<1>9. S = Part(formal[r], Cur(formal[r]))
    BY ONLY SMT, FS_Subset, <1>1, <1>6, <1>7, <1>8 DEF Count
<1> QED BY <1>1, <1>7, <1>9

THEOREM IncomingFollowerEntryHasKnownPrefix ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipBoundaryCommit,
           NEW r \in Replicas, NEW o \in offers, CanReceive(r, o),
           NEW p \in retained[r], p.epoch = term[r], p.owner # r
    PROVE \A x \in Prefix(formal[r], o.entry.part - 1) : KnownBy(commitHistory, term[r], x)
<1>1. Aligned(r, term[r])
    BY DEF CanReceive
<1>2. \A x \in Prefix(formal[r], Cur(formal[r]) - 1) : KnownBy(commitHistory, term[r], x)
    BY FollowerKnowsBeforeOpenPartition, <1>1
<1>3. CASE o.entry.part = Cur(formal[r])
    BY <1>2, <1>3
<1>4. CASE o.entry.part # Cur(formal[r])
    <2>1. \A x \in Part(formal[r], Cur(formal[r])) : KnownBy(commitHistory, term[r], x)
        BY BoundaryCountWitnessCoversPartition, <1>4
    <2>20. formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
           TypeOK, FiniteLogInvariant, FiniteNodeData
    <2>21. Cur(formal[r]) \in Int
          /\ \A e \in formal[r] : e.part \in Int /\ e.part <= Cur(formal[r])
        BY FiniteLogPartitionFrontier, <2>20
    <2>2. o.entry.part = Cur(formal[r]) + 1 /\ Cur(formal[r]) \in Int
          /\ \A e \in formal[r] : e.part \in Int
        BY <1>4, <2>21 DEF CanReceive
    <2>3. Prefix(formal[r], Cur(formal[r])) =
          Prefix(formal[r], Cur(formal[r]) - 1) \cup Part(formal[r], Cur(formal[r]))
        BY PrefixAtBoundary, <2>2
    <2> QED BY SMT, <1>2, <2>1, <2>2, <2>3
<1> QED BY <1>3, <1>4

THEOREM AppendDoesNotChangeEarlierPrefixes ==
    ASSUME NEW L, NEW added, added.part \in Int,
           \A e \in L : e.part \in Int /\ e.part <= added.part
    PROVE \A e \in L \cup {added} : Prefix(L \cup {added}, e.part - 1) = Prefix(L, e.part - 1)
BY SMT DEF Prefix

THEOREM ReceiveNodeKeepsFollowerEvidence ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipBoundaryCommit,
           NEW r \in Replicas, NEW o, ReceiveEntry(r, o), commitHistory \subseteq commitHistory'
    PROVE NodeFollowerEvidence(r, formal', term', retained', commitHistory')
<1>1. o \in offers /\ CanReceive(r, o) /\ formal'[r] = formal[r] \cup {o.entry}
      /\ term'[r] = term[r] /\ retained'[r] = retained[r]
    BY SMT DEF ReceiveEntry, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. formal[r] \subseteq Entries /\ IsFiniteSet(formal[r]) /\ o.entry \in Entries
    <2>1. formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
           FiniteLogInvariant, FiniteNodeData
    <2>2. PICK v \in leaderViews : o.entry \in v.entries
        BY <1>1 DEF ProofInvariant, OfferProvenance
    <2>3. v.epoch \in Terms /\ v.entries \subseteq canonical[v.epoch]
          /\ canonical \in [Terms -> SUBSET Entries]
        BY <2>2 DEF ProofInvariant, CanonicalViewLinks, PreProvenanceInvariant,
           RecoveryInvariant, CanonicalShape
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1>3. Cur(formal[r]) \in Int /\ \A e \in formal[r] : e.part \in Int /\ e.part <= Cur(formal[r])
    BY FiniteLogPartitionFrontier, <1>2
<1>4. o.entry.part \in Int /\ o.entry.part >= Cur(formal[r])
    BY SMT, <1>1, <1>2, <1>3 DEF CanReceive, Entries, Partitions
<1>40. \A e \in formal[r] : e.part \in Int /\ e.part <= o.entry.part
    BY ONLY SMT, <1>3, <1>4
<1>41. \A e \in formal[r] \cup {o.entry} :
          Prefix(formal[r] \cup {o.entry}, e.part - 1) = Prefix(formal[r], e.part - 1)
    BY ONLY AppendDoesNotChangeEarlierPrefixes, <1>4, <1>40
<1>5. \A e \in formal[r] \cup {o.entry} :
          Prefix(formal'[r], e.part - 1) = Prefix(formal[r], e.part - 1)
    BY ONLY <1>1, <1>41
<1>6. ASSUME NEW p \in retained'[r], p.epoch = term'[r], p.owner # r,
            NEW e \in formal'[r], e.term = term'[r]
      PROVE \A x \in Prefix(formal'[r], e.part - 1) : KnownBy(commitHistory', term'[r], x)
    <2>1. p \in retained[r] /\ p.epoch = term[r] /\ e \in formal[r] \cup {o.entry}
        BY <1>1, <1>6
    <2>2. CASE e \in formal[r]
        <3>1. \A x \in Prefix(formal[r], e.part - 1) : KnownBy(commitHistory, term[r], x)
            BY <1>1, <1>6, <2>1, <2>2 DEF ProofInvariant, PrefixEvidenceInvariant, FollowerPrefixEvidence
        <3> QED BY SMT, KnownBySurvivesHistoryGrowth, <1>1, <1>5, <2>1, <3>1
    <2>3. CASE e = o.entry
        <3>1. \A x \in Prefix(formal[r], o.entry.part - 1) : KnownBy(commitHistory, term[r], x)
            BY IncomingFollowerEntryHasKnownPrefix, <1>1, <1>6, <2>1
        <3> QED BY SMT, KnownBySurvivesHistoryGrowth, <1>1, <1>5, <2>1, <2>3, <3>1
    <2> QED BY SMT, <2>1, <2>2, <2>3
<1> QED BY <1>6 DEF NodeFollowerEvidence
=============================================================================
