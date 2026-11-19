--------------------- MODULE TRaftCertifiedPartitionProof ---------------------
EXTENDS TRaftPartitionEvidenceProof, TRaftProposalEvidenceProof

THEOREM CertifiedContextHasConfirmedEpoch ==
    ASSUME ProofInvariant, NEW ctx \in CertifiedContexts(entryContexts, leaderViews, confirmations)
    PROVE \E p \in confirmations : p \in proposals /\ p.epoch \in Terms
              /\ ctx.entry \in canonical[p.epoch]
<1>1. ctx \in entryContexts
      /\ ctx.entry \in (UNION {v.entries : v \in leaderViews}) \cup (UNION {Result(p) : p \in confirmations})
    BY DEF CertifiedContexts, CertifiedLogEntries
<1>2. confirmations \subseteq proposals
      /\ (\A v \in leaderViews : v.epoch \in Terms /\ v.entries \subseteq canonical[v.epoch])
      /\ (\A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch])
    BY DEF ProofInvariant, MessageSourceInvariant, ConfirmationSources, CanonicalViewLinks,
       PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>3. \A v \in leaderViews : \E p \in confirmations : p.epoch = v.epoch
    BY DEF ProofInvariant, PrefixEvidenceInvariant, ActiveRecoveryCertificates, LeaderViewsCertified
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3

THEOREM CertifiedClosedPartitionContainsAllEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           NEW ctx \in CertifiedContexts(entryContexts, leaderViews, confirmations),
           NEW k \in Nat, k < ctx.entry.part, Part(ctx.prefix, k) # {},
           \A e \in Part(ctx.prefix, k) : \E f \in commitHistory : f.entry = e
    PROVE \A f \in commitHistory : f.entry.part = k => f.entry \in Part(ctx.prefix, k)
<1>1. PICK p \in confirmations : p \in proposals /\ p.epoch \in Terms
          /\ ctx.entry \in canonical[p.epoch]
    BY CertifiedContextHasConfirmedEpoch
<1>2. ctx \in entryContexts /\ Part(ctx.prefix, k) = Part(canonical[p.epoch], k)
    BY ContextPartitionIsCanonical, <1>1 DEF CertifiedContexts
<1>3. p.first.part \in Nat /\ p.epoch \in Nat
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Entries, Partitions, Terms
<1>4. CASE k < p.first.part
    <2>1. Quorum(ProposalSenders(ackMessages, p)) /\ p.first \in Result(p)
        BY <1>1 DEF ProofInvariant, KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders, Result
    <2>2. [epoch |-> p.epoch, entry |-> p.first] \in commitHistory
        BY ChosenProposalHasEntryEvidence, <1>1, <2>1
    <2>3. PICK bound \in entryContexts : bound.entry = p.first
        BY SMT, <2>2 DEF EntryContextUnique
    <2>40. \A t \in Terms : \A q \in proposals : q.epoch = t => Result(q) \subseteq canonical[t]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>41. Result(p) \subseteq canonical[p.epoch]
        BY ONLY <1>1, <2>40
    <2>4. p.first \in canonical[p.epoch]
        BY ONLY SMT, <2>41 DEF Result
    <2>5. Part(bound.prefix, k) = Part(ctx.prefix, k)
        BY ContextPartitionIsCanonical, <1>1, <1>2, <1>4, <2>3, <2>4
    <2>6. \A f \in commitHistory : f.entry.part = k => f.entry \in Part(bound.prefix, k)
        BY CommittedBoundaryClosesPartition, <1>4, <2>2, <2>3
    <2> QED BY <2>5, <2>6
<1>5. CASE k >= p.first.part
    <2>1. PICK e \in Part(ctx.prefix, k) : TRUE
        BY ZenonT(5)
    <2>2. e \in canonical[p.epoch] /\ e.part = k
        BY SMT, <1>2, <2>1 DEF Part
    <2>3. e.term = p.epoch
        BY CanonicalRecoveryExtensionHasCurrentOrigin, <1>1, <1>5, <2>2
    <2>4. PICK source \in commitHistory : source.entry = e
        BY <2>1
    <2>5. ASSUME NEW f \in commitHistory, f.entry.part = k
          PROVE f.entry \in Part(ctx.prefix, k)
        <3>1. f.entry.term = p.epoch
            BY EvidencePartitionOriginsAgree, <2>2, <2>3, <2>4, <2>5
        <3>2. f.entry \in canonical[p.epoch]
            BY EvidenceEntryBelongsToCreationCanonical, <2>5, <3>1
        <3> QED BY SMT, <1>2, <2>5, <3>2 DEF Part
    <2> QED BY <2>5
<1> QED BY SMT, <1>3, <1>4, <1>5

THEOREM SubsetFromEvidenceMembership ==
    ASSUME NEW S, NEW T, NEW k, NEW H,
           \A e \in S : e.part = k /\ \E f \in H : f.entry = e,
           \A f \in H : f.entry.part = k => f.entry \in T
    PROVE S \subseteq T
<1>1. ASSUME NEW e \in S
      PROVE e \in T
    <2>1. e.part = k /\ \E f \in H : f.entry = e
        BY <1>1
    <2>2. PICK f \in H : f.entry = e
        BY <2>1
    <2>3. f.entry.part = k
        BY ONLY <2>1, <2>2
    <2> QED BY <2>2, <2>3
<1> QED BY <1>1

THEOREM CertifiedPartitionFamiliesAgree ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique, NEW H,
           ClosedPartitionOrigins(H, CertifiedContexts(entryContexts, leaderViews, confirmations)),
           \A h \in H : h.part \in Nat /\ h.entries # {}
               /\ (\A e \in h.entries : e.part = h.part /\ \E f \in commitHistory : f.entry = e)
    PROVE \A a, b \in H : a.part = b.part => a.entries = b.entries
<1>0. \A h \in H : h.part \in Nat /\ h.entries # {}
          /\ (\A e \in h.entries : e.part = h.part /\ \E f \in commitHistory : f.entry = e)
    OBVIOUS
<1>1. ASSUME NEW a \in H, NEW b \in H, a.part = b.part
      PROVE a.entries = b.entries
    <2>1. PICK ca \in CertifiedContexts(entryContexts, leaderViews, confirmations) :
              ca.entry.part > a.part /\ Part(ca.prefix, a.part) = a.entries
        BY <1>1 DEF ClosedPartitionOrigins, HasClosedContext
    <2>2. PICK cb \in CertifiedContexts(entryContexts, leaderViews, confirmations) :
              cb.entry.part > b.part /\ Part(cb.prefix, b.part) = b.entries
        BY <1>1 DEF ClosedPartitionOrigins, HasClosedContext
    <2>3. \A f \in commitHistory : f.entry.part = a.part => f.entry \in a.entries
        BY CertifiedClosedPartitionContainsAllEvidence, <1>1, <2>1
    <2>4. \A f \in commitHistory : f.entry.part = b.part => f.entry \in b.entries
        BY CertifiedClosedPartitionContainsAllEvidence, <1>1, <2>2
    <2>50. \A e \in a.entries : e.part = a.part /\ \E f \in commitHistory : f.entry = e
        BY ONLY <1>0, <1>1
    <2>51. \A e \in b.entries : e.part = a.part /\ \E f \in commitHistory : f.entry = e
        BY ONLY <1>0, <1>1
    <2>52. \A f \in commitHistory : f.entry.part = a.part => f.entry \in b.entries
        BY ONLY <1>1, <2>4
    <2>5. a.entries \subseteq b.entries
        BY ONLY SubsetFromEvidenceMembership, <2>50, <2>52
    <2>6. b.entries \subseteq a.entries
        BY ONLY SubsetFromEvidenceMembership, <2>51, <2>3
    <2> QED BY ONLY ZenonT(5), <2>5, <2>6
<1> QED BY <1>1

THEOREM CandidateCommittedPartitionsAgree ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique) => CommittedPartitionAgreement
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique
      PROVE CommittedPartitionAgreement
    <2>1. ClosedPartitionOrigins(partitionHistory, CertifiedContexts(entryContexts, leaderViews, confirmations))
        BY <1>1 DEF ProofInvariant, CertifiedPartitionHistory
    <2>2. PartitionHistoryOrigins
        BY <1>1 DEF ProofInvariant, HistoryOriginInvariant
    <2>30. Partitions \subseteq Nat
        BY ParameterAssumptions DEF ParameterAssumptions
    <2>3. \A h \in partitionHistory : h.part \in Nat /\ h.entries # {}
              /\ (\A e \in h.entries : e.part = h.part /\ \E f \in commitHistory : f.entry = e)
        BY ONLY ZenonT(10), <2>2, <2>30 DEF PartitionHistoryOrigins
    <2> QED BY CertifiedPartitionFamiliesAgree, <1>1, <2>1, <2>3 DEF CommittedPartitionAgreement
<1> QED BY <1>1

THEOREM CandidateAppliedPartitionsAgree ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique) => PartitionStateMachineSafety
BY SMT, CertifiedPartitionFamiliesAgree DEF ProofInvariant, CertifiedPartitionHistory,
    HistoryOriginInvariant, AppliedPartitionOrigins, AppliedEvidence, PartitionStateMachineSafety
=============================================================================
