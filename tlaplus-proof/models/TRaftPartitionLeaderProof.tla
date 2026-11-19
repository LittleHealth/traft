----------------------- MODULE TRaftPartitionLeaderProof ----------------------
EXTENDS TRaftCertifiedPartitionProof

THEOREM EvidenceAuthorizationBoundsCreationTerm ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW f \in commitHistory
    PROVE f.entry.term \in Nat /\ f.epoch \in Nat /\ f.entry.term <= f.epoch
<1>1. f.epoch \in Terms /\ f.entry \in canonical[f.epoch]
    BY EvidenceIsPossible, EvidenceHasCanonicalSource
<1> QED BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, TypeOK, Entries, Terms

THEOREM CandidatePartitionLeaderCompleteness ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique) => PartitionLeaderCompleteness
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
            NEW h \in partitionHistory, NEW v \in leaderViews, v.epoch > h.epoch
      PROVE Part(v.entries, h.part) = h.entries
    <2>1. EntryLeaderCompleteness
        BY CandidateImpliesEntryLeaderCompleteness, <1>1
    <2>2. h.part \in Nat /\ h.epoch \in Nat /\ v.epoch \in Terms /\ v.epoch \in Nat
          /\ h.entries # {} /\ v.entries \subseteq canonical[v.epoch]
          /\ (\A e \in h.entries : e.part = h.part /\
                  \E f \in commitHistory : f.entry = e /\ f.epoch <= h.epoch)
        BY SMT, <1>1 DEF ProofInvariant, HistoryOriginInvariant, PartitionHistoryOrigins,
           CanonicalViewLinks, Partitions, Terms
    <2>3. \A f \in commitHistory : f.epoch \in Nat
        BY SMT, <1>1 DEF CommitEvidenceSound, Evidence, Terms
    <2>4. h.entries \subseteq Part(v.entries, h.part)
        BY ONLY SMT, <1>1, <2>1, <2>2, <2>3 DEF EntryLeaderCompleteness, Part
    <2>5. PICK p \in confirmations : p.epoch = v.epoch
        BY <1>1 DEF ProofInvariant, PrefixEvidenceInvariant, ActiveRecoveryCertificates, LeaderViewsCertified
    <2>6. p \in proposals /\ p.first.part \in Nat
        BY SMT, <1>1, <2>5 DEF ProofInvariant, MessageSourceInvariant, ConfirmationSources,
           PreProvenanceInvariant, RecoveryInvariant, TypeOK, Entries, Partitions
    <2>7. PICK e \in h.entries : TRUE
        BY ZenonT(5), <2>2
    <2>8. PICK f \in commitHistory : f.entry = e /\ f.epoch <= h.epoch
        BY <2>2, <2>7
    <2>9. e \in canonical[p.epoch] /\ e.part = h.part /\ e.term \in Nat /\ e.term <= f.epoch
        BY SMT, EvidenceAuthorizationBoundsCreationTerm, <1>1, <2>2, <2>4, <2>5, <2>7, <2>8 DEF Part
    <2>10. h.part < p.first.part
        <3>1. h.part >= p.first.part => e.term = p.epoch
            BY CanonicalRecoveryExtensionHasCurrentOrigin, <1>1, <2>6, <2>9
        <3> QED BY ONLY SMT, <1>1, <2>2, <2>3, <2>5, <2>6, <2>8, <2>9, <3>1
    <2>11. \A x \in canonical[p.epoch] \ Result(p) : x.part >= p.first.part
        BY <1>1, <2>2, <2>5, <2>6 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>12. Part(v.entries, h.part) \subseteq Result(p)
        BY ONLY SMT, <2>2, <2>5, <2>6, <2>10, <2>11 DEF Part
    <2>13. Quorum(ProposalSenders(ackMessages, p))
        BY <1>1, <2>5 DEF ProofInvariant, KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders
    <2>14. \A x \in Part(v.entries, h.part) : [epoch |-> p.epoch, entry |-> x] \in commitHistory
        BY ChosenProposalHasEntryEvidence, <1>1, <2>6, <2>12, <2>13
    <2>15. PICK ctx \in CertifiedContexts(entryContexts, leaderViews, confirmations) :
               ctx.entry.part > h.part /\ Part(ctx.prefix, h.part) = h.entries
        BY <1>1 DEF ProofInvariant, CertifiedPartitionHistory, ClosedPartitionOrigins, HasClosedContext
    <2>16. \A g \in commitHistory : g.entry.part = h.part => g.entry \in h.entries
        BY CertifiedClosedPartitionContainsAllEvidence, <1>1, <2>2, <2>15
    <2>17. \A x \in Part(v.entries, h.part) :
               x.part = h.part /\ \E g \in commitHistory : g.entry = x
        <3>1. ASSUME NEW x \in Part(v.entries, h.part)
              PROVE x.part = h.part /\ \E g \in commitHistory : g.entry = x
            <4>1. x.part = h.part /\ [epoch |-> p.epoch, entry |-> x] \in commitHistory
                BY ONLY <2>14, <3>1 DEF Part
            <4>2. [epoch |-> p.epoch, entry |-> x].entry = x
                BY SMT
            <4> QED BY ONLY <4>1, <4>2
        <3> QED BY <3>1
    <2>18. Part(v.entries, h.part) \subseteq h.entries
        BY ONLY SubsetFromEvidenceMembership, <2>16, <2>17
    <2> QED BY ONLY ZenonT(5), <2>4, <2>18
<1> QED BY <1>1 DEF PartitionLeaderCompleteness
=============================================================================
