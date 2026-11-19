--------------------- MODULE TRaftSafetyAppliedPreservation -------------------
EXTENDS TRaftPotentialCoverageProof, TRaftEvidenceTermOrderProof, TRaftApplicationOrderProof

THEOREM FormalChangeHasConfirmedPublishSource ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE \A r \in Replicas : formal[r] \subseteq formal'[r] \/
        \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p) /\ p \in confirmations'
<1>1. TypeOK /\ (FormalAnchorChanges \/ UNCHANGED formal)
    BY FormalAnchorActionProjection DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>2. \A c \in Replicas : \A v, k :
          (CreateEntry(c, v) \/ CreateSuccessor(c, v, k)) =>
              \A r \in Replicas : formal[r] \subseteq formal'[r]
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, TypeOK
<1>3. \A c \in Replicas : \A o : ReceiveEntry(c, o) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r]
    BY SMT, <1>1 DEF ReceiveEntry, TypeOK
<1>4. \A c \in Replicas : ConfirmProposal(c) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r] \/
              \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p) /\ p \in confirmations'
    BY SMT, <1>1 DEF ConfirmProposal, TypeOK
<1>5. \A c \in Replicas : \A p : LearnConfirmation(c, p) =>
          \A r \in Replicas : formal[r] \subseteq formal'[r] \/
              \E q \in retained[r] : q.epoch = term[r] /\ formal'[r] = Publish(r, q) /\ q \in confirmations'
    BY SMT, <1>1 DEF LearnConfirmation, TypeOK
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5 DEF FormalAnchorChanges

THEOREM ConfirmedPublishRetainsApplied ==
    ASSUME Inv, ProofInvariant', CommitEvidenceSound', EntryContextUnique',
           commitHistory \subseteq commitHistory', NEW r \in Replicas,
           NEW p \in retained[r], p.epoch = term[r], p \in confirmations',
           formal'[r] = Publish(r, p)
    PROVE applied[r] \subseteq formal'[r]
<1>00. ProofInvariant /\ AppliedEntriesPreserved
    BY DEF Inv, Safety
<1>01. TypeOK /\ CanonicalShape /\ AppliedEvidence
    BY <1>00 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, HistoryOriginInvariant
<1>02. formal[r] \subseteq Entries /\ term[r] \in Terms
      /\ \A e \in formal[r] : e.term <= term[r]
    BY <1>01 DEF TypeOK, CanonicalShape
<1>03. term[r] \in Nat /\ \A e \in formal[r] : e.term \in Nat
    BY ONLY SMT, <1>02 DEF Entries, Terms
<1>1. ProofInvariant /\ applied[r] \subseteq formal[r]
      /\ term[r] \in Nat
      /\ (\A e \in formal[r] : e.term \in Nat /\ e.term <= term[r])
      /\ (\A e \in applied[r] : \E f \in commitHistory : f.entry = e)
    BY ONLY SMT, <1>00, <1>01, <1>02, <1>03 DEF AppliedEntriesPreserved, AppliedEvidence
<1>2. ConfirmedProposalsIncludeEarlierCreationEvidence'
    BY ONLY PTL, ConfirmedProposalsIncludeEarlierCreationEvidence
<1>3. \A q \in confirmations' : \A f \in commitHistory' : f.entry.term < q.epoch => f.entry \in q.prefix
    BY <1>2
<1>4. ASSUME NEW e \in applied[r]
      PROVE e \in formal'[r]
    <2>1. CASE p.first \in formal[r]
        BY <1>1, <1>4, <2>1 DEF Publish
    <2>2. CASE p.first \notin formal[r]
        <3>1. e \in formal[r] /\ e.term \in Nat /\ e.term <= p.epoch /\ p.epoch \in Nat
            BY <1>1, <1>4
        <3>2. e.term # p.epoch
            BY CurrentFormalEntryPinsProposal, <1>1, <3>1, <2>2
        <3>3. PICK f \in commitHistory : f.entry = e
            BY <1>1, <1>4
        <3>4. f \in commitHistory' /\ e.term < p.epoch
            BY SMT, <3>1, <3>2, <3>3
        <3>5. e \in p.prefix
            BY <1>3, <3>3, <3>4
        <3> QED BY SMT, <2>2, <3>5 DEF Publish, Result
    <2> QED BY <2>1, <2>2
<1> QED BY <1>4

THEOREM AppliedEntriesPreservedInductiveStep ==
    ASSUME Inv, ProofNext, ProofInvariant', CommitEvidenceSound', EntryContextUnique'
    PROVE AppliedEntriesPreserved'
<1>1. ProofInvariant /\ ProtocolNext /\ commitHistory \subseteq commitHistory'
      /\ AppliedEntriesPreserved /\ TypeOK
    BY SMT DEF Inv, Safety, ProofNext, Next, Observe, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>2. \A r \in Replicas : formal[r] \subseteq formal'[r] \/
          \E p \in retained[r] : p.epoch = term[r] /\ formal'[r] = Publish(r, p) /\ p \in confirmations'
    BY FormalChangeHasConfirmedPublishSource, <1>1
<1>3. \A r \in Replicas : applied[r] \subseteq formal'[r]
    BY SMT, ConfirmedPublishRetainsApplied, <1>1, <1>2 DEF AppliedEntriesPreserved
<1>4. (\E r \in Replicas : \E e : ApplyEntry(r, e)) \/ UNCHANGED applied
    BY OnlyApplyChangesApplied, <1>1
<1>5. \A r \in Replicas : \A e : ApplyEntry(r, e) => AppliedEntriesPreserved'
    BY SMT, <1>1 DEF ApplyEntry, AppliedEntriesPreserved, TypeOK
<1> QED BY SMT, <1>3, <1>4, <1>5 DEF AppliedEntriesPreserved
=============================================================================
