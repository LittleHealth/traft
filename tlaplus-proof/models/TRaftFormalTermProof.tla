-------------------------- MODULE TRaftFormalTermProof -----------------------
EXTENDS TRaftOriginFrames, TRaftTermAndVoteProof

LogTermBound(L, t) == \A e \in L : e.term \in Nat /\ e.term <= t
FormalTermBounds(F, T) == \A r \in Replicas : LogTermBound(F[r], T[r])

THEOREM TermFunctionIsNatural ==
    ASSUME NEW T \in [Replicas -> Terms]
    PROVE T \in [Replicas -> Nat]
<1>1. Terms \subseteq Nat
    BY ParameterAssumptions DEF ParameterAssumptions
<1> QED BY ONLY ZenonT(5), <1>1

THEOREM CandidateHasFormalTermBounds == ProofInvariant => FormalTermBounds(formal, term)
<1>1. ASSUME ProofInvariant
      PROVE FormalTermBounds(formal, term)
    <2>1. formal \in [Replicas -> SUBSET Entries]
          /\ \A r \in Replicas : \A e \in formal[r] : e.term <= term[r]
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
    <2> QED BY ONLY SMT, <2>1 DEF FormalTermBounds, LogTermBound, Entries, Terms
<1> QED BY <1>1

THEOREM PublishedLogHasTermBound ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p \in proposals, p.epoch = term[r]
    PROVE LogTermBound(Publish(r, p), term[r])
<1>1. FormalTermBounds(formal, term)
    BY CandidateHasFormalTermBounds
<1>20. p \in proposals /\ p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>21. canonical \in [Terms -> SUBSET Entries]
      /\ \A t \in Terms : \A e \in canonical[t] : e.term <= t
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>2. p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
      /\ canonical[p.epoch] \subseteq Entries
      /\ \A e \in canonical[p.epoch] : e.term <= p.epoch
    BY ONLY SMT, <1>20, <1>21
<1>3. LogTermBound(Result(p), term[r])
    BY SMT, <1>2 DEF LogTermBound, Entries, Terms
<1> QED BY <1>1, <1>3 DEF FormalTermBounds, Publish

THEOREM FormalChangesKeepOldTermBounds ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE FormalTermBounds(formal', term)
<1>00. TypeOK
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>10. FormalTermBounds(formal, term) /\ (FormalAnchorChanges \/ UNCHANGED formal)
    BY CandidateHasFormalTermBounds, FormalAnchorActionProjection, <1>00
<1>11. formal \in [Replicas -> SUBSET Entries]
      /\ retained \in [Replicas -> SUBSET proposals] /\ term \in [Replicas -> Terms]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>12. Terms \subseteq Nat
    BY ParameterAssumptions DEF ParameterAssumptions
<1>13. term \in [Replicas -> Nat]
    BY TermFunctionIsNatural, <1>11
<1>1. FormalTermBounds(formal, term) /\ formal \in [Replicas -> SUBSET Entries]
      /\ retained \in [Replicas -> SUBSET proposals] /\ term \in [Replicas -> Nat]
      /\ (FormalAnchorChanges \/ UNCHANGED formal)
    BY ONLY <1>10, <1>11, <1>13
<1>2. \A c \in Replicas : \A v, k : (CreateEntry(c, v) \/ CreateSuccessor(c, v, k)) =>
          FormalTermBounds(formal', term)
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, Entry, FormalTermBounds, LogTermBound
<1>3. \A r \in Replicas : \A o : ReceiveEntry(r, o) => FormalTermBounds(formal', term)
    <2>1. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
          PROVE FormalTermBounds(formal', term)
        <3>1. o \in offers /\ o.epoch = term[r]
            BY <2>1 DEF ReceiveEntry, CanReceive
        <3>2. o.entry.term = term[r]
            BY <3>1 DEF ProofInvariant, OfferProvenance
        <3> QED BY SMT, <1>1, <2>1, <3>2 DEF ReceiveEntry, FormalTermBounds, LogTermBound
    <2> QED BY <2>1
<1>4. \A c \in Replicas : ConfirmProposal(c) => FormalTermBounds(formal', term)
    BY SMT, PublishedLogHasTermBound, <1>1 DEF ConfirmProposal, FormalTermBounds
<1>5. \A r \in Replicas : \A p : LearnConfirmation(r, p) => FormalTermBounds(formal', term)
    BY SMT, PublishedLogHasTermBound, <1>1 DEF LearnConfirmation, FormalTermBounds
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5 DEF FormalAnchorChanges, FormalTermBounds

THEOREM FormalTermBoundsInductiveStep ==
    ASSUME ProofInvariant, ProofNext, TypeOK'
    PROVE FormalTermBounds(formal', term')
<1>0. ProtocolNext
    BY DEF ProofNext, Next
<1>10. StepFacts
    BY CandidateStepHasMonotonicFacts, <1>0
<1>11. term \in [Replicas -> Terms] /\ term' \in [Replicas -> Terms]
    BY DEF TypeOK, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>12. Terms \subseteq Nat
    BY ParameterAssumptions DEF ParameterAssumptions
<1>13. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
    BY TermFunctionIsNatural, <1>11
<1>1. ProtocolNext /\ StepFacts /\ term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
    BY ONLY <1>0, <1>10, <1>13
<1>2. FormalTermBounds(formal', term)
    BY FormalChangesKeepOldTermBounds, <1>1
<1> QED BY ONLY SMT, <1>1, <1>2 DEF StepFacts, FormalTermBounds, LogTermBound
=============================================================================
