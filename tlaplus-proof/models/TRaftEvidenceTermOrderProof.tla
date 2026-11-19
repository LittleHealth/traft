--------------------- MODULE TRaftEvidenceTermOrderProof ----------------------
EXTENDS TRaftPartitionEvidenceProof, TRaftProposalEvidenceProof

THEOREM EvidenceTermsOrderPartitions ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           NEW a \in commitHistory, NEW b \in commitHistory, a.entry.term < b.entry.term
    PROVE a.entry.part < b.entry.part
<1>1. PICK t \in Terms : a.entry \in canonical[t] /\ b.entry \in canonical[t]
    BY TwoEvidenceEntriesHaveCommonCanonical
<1>2. a.entry \in Entries /\ b.entry \in Entries /\ ContextSound(canonical[t])
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>3. a.entry.part # b.entry.part
    BY SMT, EvidencePartitionOriginsAgree, <1>2 DEF Entries, Terms
<1>4. ASSUME a.entry.part > b.entry.part
      PROVE FALSE
    <2>1. PICK ctx \in entryContexts : ctx.entry = a.entry
              /\ ctx.prefix = Prefix(canonical[t], a.entry.part - 1)
        BY SMT, <1>1, <1>2 DEF ContextSound
    <2>2. b.entry \in ctx.prefix
        BY SMT, <1>1, <1>2, <1>4, <2>1 DEF Entries, Partitions, Prefix
    <2>3. ctx.entry.term \in Terms
          /\ ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
        BY ContextOriginIdentifiesCanonicalPrefix, <2>1
           DEF ProofInvariant, ContextOrigins, PreProvenanceInvariant, RecoveryInvariant
    <2>4. b.entry \in canonical[a.entry.term]
        BY SMT, <2>1, <2>2, <2>3 DEF Prefix
    <2>5. b.entry.term <= a.entry.term
        BY <2>1, <2>3, <2>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2> QED BY SMT, <1>2, <2>5 DEF Entries, Terms
<1> QED BY SMT, <1>2, <1>3, <1>4 DEF Entries, Partitions

THEOREM ConfirmedProposalsIncludeEarlierCreationEvidence ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique) =>
        \A p \in confirmations : \A f \in commitHistory : f.entry.term < p.epoch => f.entry \in p.prefix
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
            NEW p \in confirmations, NEW f \in commitHistory, f.entry.term < p.epoch
      PROVE f.entry \in p.prefix
    <2>1. p \in proposals /\ Quorum(ProposalSenders(ackMessages, p)) /\ p.first \in Result(p)
        BY <1>1 DEF ProofInvariant, MessageSourceInvariant, ConfirmationSources,
           KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders, Result
    <2>2. [epoch |-> p.epoch, entry |-> p.first] \in commitHistory
        BY ChosenProposalHasEntryEvidence, <1>1, <2>1
    <2>30. \A q \in proposals : q.first.term = q.epoch /\ q.epoch \in Terms
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>31. \A t \in Terms : ContextSound(canonical[t])
          /\ (\A q \in proposals : q.epoch = t =>
                Result(q) \subseteq canonical[t] /\ Prefix(canonical[t], q.first.part - 1) = q.prefix)
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>3. p.first.term = p.epoch /\ p.epoch \in Terms
          /\ p.prefix = Prefix(canonical[p.epoch], p.first.part - 1)
          /\ p.first \in canonical[p.epoch] /\ ContextSound(canonical[p.epoch])
        BY ONLY SMT, <2>1, <2>30, <2>31 DEF Result
    <2>4. f.entry.part < p.first.part
        BY EvidenceTermsOrderPartitions, <1>1, <2>2, <2>3
    <2>5. PICK ctx \in entryContexts : ctx.entry = p.first /\ ctx.prefix = p.prefix
        BY SMT, <2>3 DEF ContextSound
    <2>6. f.entry \in Entries /\ f.entry.part \in Nat
        BY SMT, EvidenceEntryBelongsToCreationCanonical, <1>1
           DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Entries, Partitions
    <2>7. f.entry \in Part(ctx.prefix, f.entry.part)
        BY CommittedBoundaryClosesPartition, <1>1, <2>2, <2>4, <2>5, <2>6
    <2> QED BY SMT, <2>5, <2>7 DEF Part
<1> QED BY <1>1
=============================================================================
