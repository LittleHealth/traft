----------------------- MODULE TRaftHistoryOriginProof -----------------------
EXTENDS TRaftHistoryOriginState, TRaftApplicationOrderProof, TRaftCommitTemporal
USE CommitFaultsDisabled DEF CommitFaultsDisabled

THEOREM AppliedGrowsAndHasSource ==
    ASSUME AppliedShape, ProtocolNext
    PROVE OrderCheck
<1>1. (\E r \in Replicas : \E e : ApplyEntry(r, e)) \/ UNCHANGED applied
    BY OnlyApplyChangesApplied
<1>2. CASE UNCHANGED applied
    BY SMT, <1>2 DEF OrderCheck
<1>3. CASE \E r \in Replicas : \E e : ApplyEntry(r, e)
    BY ApplyEntryEstablishesOrderFacts, <1>3 DEF OrderFacts
<1> QED BY <1>1, <1>2, <1>3

THEOREM HistoriesInitiallyHaveOrigin == Init => HistoryOriginInvariant
BY SMT DEF Init, HistoryOriginInvariant, AppliedEvidence, AppliedPartitionOrigins, PartitionHistoryOrigins

THEOREM AppliedEvidenceStep ==
    ASSUME AppliedEvidence, CommittedKnowledgeSound, OrderCheck, Observe
    PROVE AppliedEvidence'
<1>1. commitHistory \subseteq commitHistory'
    BY SMT DEF Observe
<1>2. \A r \in Replicas : \A e \in applied'[r] :
          e \in applied[r] \/ e \in knownCommitted[r]
    BY SMT DEF OrderCheck
<1> QED BY SMT, <1>1, <1>2 DEF AppliedEvidence, CommittedKnowledgeSound

THEOREM AppliedPartitionOriginsStep ==
    ASSUME AppliedPartitionOrigins, OrderCheck, Observe
    PROVE AppliedPartitionOrigins'
<1>1. \A h \in appliedPartitionHistory :
          /\ h.node \in Replicas /\ h.part \in Nat /\ h.entries # {}
          /\ h.entries \subseteq applied'[h.node]
          /\ \A e \in h.entries : e.part = h.part
    BY SMT DEF AppliedPartitionOrigins, OrderCheck
<1>2. \A r \in Replicas : \A q \in 0..(Cur(formal'[r]) - 1) :
          (Part(formal'[r], q) # {} /\ Part(formal'[r], q) \subseteq applied'[r]) =>
            /\ r \in Replicas /\ q \in Nat /\ Part(formal'[r], q) # {}
            /\ Part(formal'[r], q) \subseteq applied'[r]
            /\ \A e \in Part(formal'[r], q) : e.part = q
    BY SMT DEF Part
<1>3. appliedPartitionHistory' = appliedPartitionHistory \cup
         (UNION { {[node |-> r, part |-> q, entries |-> Part(formal'[r], q)] :
                    q \in {j \in 0..(Cur(formal'[r]) - 1) :
                        /\ Part(formal'[r], j) # {}
                        /\ Part(formal'[r], j) \subseteq applied'[r]}} :
                  r \in Replicas })
    BY DEF Observe
<1>4. ASSUME NEW h \in appliedPartitionHistory'
      PROVE /\ h.node \in Replicas /\ h.part \in Nat /\ h.entries # {}
            /\ h.entries \subseteq applied'[h.node]
            /\ \A e \in h.entries : e.part = h.part
    <2>1. CASE h \in appliedPartitionHistory
        BY ONLY <1>1, <1>4, <2>1
    <2>2. CASE h \notin appliedPartitionHistory
        <3>1. PICK r \in Replicas : h \in
            {[node |-> r, part |-> q, entries |-> Part(formal'[r], q)] :
                q \in {j \in 0..(Cur(formal'[r]) - 1) :
                    Part(formal'[r], j) # {} /\ Part(formal'[r], j) \subseteq applied'[r]}}
            BY ONLY ZenonT(10), <1>3, <1>4, <2>2
        <3>2. PICK q \in 0..(Cur(formal'[r]) - 1) :
            /\ Part(formal'[r], q) # {} /\ Part(formal'[r], q) \subseteq applied'[r]
            /\ h = [node |-> r, part |-> q, entries |-> Part(formal'[r], q)]
            BY ONLY ZenonT(10), <3>1
        <3>3. r \in Replicas /\ q \in Nat /\ Part(formal'[r], q) # {}
              /\ Part(formal'[r], q) \subseteq applied'[r]
              /\ \A e \in Part(formal'[r], q) : e.part = q
            BY ONLY <1>2, <3>1, <3>2
        <3> QED BY ONLY SMT, <3>2, <3>3
    <2> QED BY <2>1, <2>2
<1> QED BY ONLY <1>4 DEF AppliedPartitionOrigins

THEOREM PartitionHistoryOriginsStep ==
    ASSUME PartitionHistoryOrigins, Observe
    PROVE PartitionHistoryOrigins'
<1>1. commitHistory \subseteq commitHistory'
    BY SMT DEF Observe
<1>2. \A h \in partitionHistory :
          /\ h.epoch \in Terms \ {0} /\ h.part \in Partitions /\ h.entries # {}
          /\ \A e \in h.entries :
                /\ e.part = h.part
                /\ \E f \in commitHistory' : f.entry = e /\ f.epoch <= h.epoch
    BY SMT, <1>1 DEF PartitionHistoryOrigins
<1> QED BY SMT, <1>2 DEF PartitionHistoryOrigins, Observe, Part

THEOREM HistoryOriginsInductiveStep ==
    ASSUME HistoryOriginInvariant, AppliedShape, CommittedKnowledgeSound, Next
    PROVE HistoryOriginInvariant'
<1>1. OrderCheck /\ Observe
    BY AppliedGrowsAndHasSource DEF Next
<1> QED BY AppliedEvidenceStep, AppliedPartitionOriginsStep, PartitionHistoryOriginsStep, <1>1
    DEF HistoryOriginInvariant

THEOREM HistoryOriginsStuttering ==
    ASSUME HistoryOriginInvariant, UNCHANGED vars
    PROVE HistoryOriginInvariant'
BY SMT DEF HistoryOriginInvariant, AppliedEvidence, AppliedPartitionOrigins,
   PartitionHistoryOrigins, vars, protocolVars, observerVars

THEOREM ProtocolHistoryOrigins == Spec => []HistoryOriginInvariant
<1>1. Spec => []AppliedShape /\ []CommittedKnowledgeSound
    BY PTL, ProtocolApplicationOrder, ProtocolCommitKnowledgeSound DEF OrderInvariant
<1>2. Init => HistoryOriginInvariant
    BY HistoriesInitiallyHaveOrigin
<1>3. HistoryOriginInvariant /\ AppliedShape /\ CommittedKnowledgeSound /\ [Next]_vars =>
          HistoryOriginInvariant'
    BY HistoryOriginsInductiveStep, HistoryOriginsStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec

THEOREM EvidenceAgreementImpliesStateMachineSafety ==
    (AppliedEvidence /\ CommitEvidenceAgreement) => StateMachineSafety
BY SMT DEF AppliedEvidence, CommitEvidenceAgreement, StateMachineSafety
=============================================================================
