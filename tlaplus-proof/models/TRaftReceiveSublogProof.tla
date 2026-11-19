------------------------ MODULE TRaftReceiveSublogProof ----------------------
EXTENDS TRaftSublogSupport

THEOREM ReceiveKeepsCanonicalSublog ==
    ASSUME ProofInvariant, EntryContextUnique,
           NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
    PROVE SublogIn(formal'[r], canonical, proposals)
<1>1. o \in offers /\ CanReceive(r, o) /\ o.epoch = term[r] /\ Aligned(r, term[r])
      /\ formal \in [Replicas -> SUBSET Entries] /\ term[r] \in Terms
      /\ IsFiniteSet(formal[r])
    BY SMT DEF ReceiveEntry, CanReceive, ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, TypeOK, FiniteLogInvariant, FiniteNodeData
<1>2. formal[r] # {} /\ LastTerm(formal[r]) = term[r]
    BY AlignmentIdentifiesSublogEpoch, <1>1
<1>3. formal[r] \subseteq canonical[term[r]]
      /\ \E p \in proposals : p.epoch = term[r] /\ Result(p) \subseteq formal[r]
    BY SMT, <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Sublog
<1>4. o.entry \in canonical[term[r]] /\ canonical[term[r]] \subseteq Entries
      /\ ContextSound(canonical[term[r]])
    BY SMT, <1>1 DEF ProofInvariant, OfferProvenance, CanonicalViewLinks,
       PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>5. formal'[r] = formal[r] \cup {o.entry} /\ formal'[r] \subseteq canonical[term[r]]
      /\ formal'[r] \subseteq Entries /\ IsFiniteSet(formal'[r])
    BY SMT, FS_AddElement, <1>1, <1>3, <1>4 DEF ReceiveEntry
<1>6. PICK p \in proposals : p.epoch = term[r] /\ Result(p) \subseteq formal[r]
    BY <1>3
<1>7. LastTerm(formal'[r]) = term[r]
    BY AnchoredCanonicalSubsetHasCurrentLastTerm, <1>5, <1>6 DEF Result
<1>8. Cur(formal[r]) \in Int /\ \A x \in formal[r] : x.part \in Int /\ x.part <= Cur(formal[r])
    BY FiniteLogPartitionFrontier, <1>1
<1>9. o.entry.part \in Int /\ o.entry.part >= Cur(formal[r])
    BY SMT, <1>1, <1>4, <1>8 DEF CanReceive, Entries, Partitions
<1>10. Cur(formal'[r]) = o.entry.part
    BY SMT, GreatestPartitionDeterminesCur, <1>5, <1>8, <1>9
<1>11. PICK ctx \in entryContexts : ctx.entry = o.entry
           /\ ctx.prefix = Prefix(canonical[term[r]], o.entry.part - 1)
    BY SMT, <1>4 DEF ContextSound
<1>12. Prefix(formal[r], o.entry.part - 1) = ctx.prefix
    BY NormalBoundaryUsesCompleteCommonPrefix, <1>1, <1>11
<1>13. Prefix(formal'[r], Cur(formal'[r]) - 1) = Prefix(canonical[term[r]], Cur(formal'[r]) - 1)
    BY ONLY SMT, <1>5, <1>9, <1>10, <1>11, <1>12 DEF Prefix
<1> QED BY SMT, <1>1, <1>5, <1>6, <1>7, <1>13 DEF SublogIn
=============================================================================
