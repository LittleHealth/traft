---------------------- MODULE TRaftRecoveryContextProof ----------------------
EXTENDS TRaftBoundaryCountSupport, TRaftContextOriginProof

THEOREM RecoveryResultContainsEntryContext ==
    ASSUME ProofInvariant, EntryContextUnique, NEW p \in proposals,
           NEW ctx \in entryContexts, ctx.entry \in Result(p)
    PROVE ctx.prefix \subseteq Result(p)
<1>00. p \in proposals /\ ctx \in entryContexts /\ ctx.entry \in Result(p)
    OBVIOUS
<1>01. \A q \in proposals : q.epoch \in Terms \ {0}
          /\ q.prefix \subseteq Entries /\ q.first.part = Cur(q.prefix) + 1
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>02. canonical \in [Terms -> SUBSET Entries]
      /\ (\A t \in Terms : ContextSound(canonical[t]))
      /\ (\A t \in Terms : \A q \in proposals : q.epoch = t =>
            Result(q) \subseteq canonical[t] /\ Prefix(canonical[t], q.first.part - 1) = q.prefix)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>03. \A q \in proposals : IsFiniteSet(Result(q))
    BY DEF ProofInvariant, PreProvenanceInvariant, FiniteLogInvariant, FiniteProposals
<1>1. p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
      /\ ContextSound(canonical[p.epoch])
      /\ Prefix(canonical[p.epoch], p.first.part - 1) = p.prefix
    BY ONLY SMT, <1>00, <1>01, <1>02
<1>21. IsFiniteSet(Result(p))
    BY ONLY <1>00, <1>03
<1>22. p.prefix \subseteq Result(p)
    BY SMT DEF Result
<1>23. IsFiniteSet(p.prefix)
    BY ONLY ZenonT(5), FS_Subset, <1>21, <1>22
<1>2. p.prefix \subseteq Entries /\ IsFiniteSet(p.prefix)
      /\ p.first.part = Cur(p.prefix) + 1
    BY ONLY <1>00, <1>01, <1>23
<1>3. Cur(p.prefix) \in Int /\ \A e \in p.prefix : e.part \in Int /\ e.part <= Cur(p.prefix)
    BY FiniteLogPartitionFrontier, <1>2
<1>4. ctx.entry.part \in Int /\ p.first.part \in Int /\ ctx.entry.part <= p.first.part
    BY SMT, <1>2, <1>3 DEF Result
<1>5. PICK source \in entryContexts : source.entry = ctx.entry
          /\ source.prefix = Prefix(canonical[p.epoch], ctx.entry.part - 1)
    BY SMT, <1>1 DEF ContextSound
<1>6. ctx.prefix = Prefix(canonical[p.epoch], ctx.entry.part - 1)
    BY SMT, <1>5 DEF EntryContextUnique
<1>7. canonical[p.epoch] \subseteq Entries
    BY ONLY SMT, <1>1, <1>02
<1>8. ctx.prefix \subseteq p.prefix
    BY ONLY SMT, <1>1, <1>4, <1>6, <1>7 DEF Prefix, Entries, Partitions
<1> QED BY ONLY SMT, <1>8 DEF Result

=============================================================================
