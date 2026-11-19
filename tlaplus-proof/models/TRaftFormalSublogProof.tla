------------------------ MODULE TRaftFormalSublogProof -----------------------
EXTENDS TRaftReceiveSublogProof, TRaftLeaderCanonicalProof, TRaftOriginFrames,
        TRaftTermAndVoteProof, TRaftNormalSublogProof, TRaftHistoryRefinementProof

FormalSublogs(F, C, P) == \A r \in Replicas : SublogIn(F[r], C, P)
FormalOldOrFullSource == \A r \in Replicas :
    SublogIn(formal'[r], canonical, proposals) \/
    (/\ role'[r] = "Leader" /\ LastTerm(formal'[r]) = term'[r]
     /\ \E p \in proposals' : p.epoch = term'[r] /\ Result(p) \subseteq formal'[r])

THEOREM PublishedLogIsOldCanonicalSublog ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p \in proposals
    PROVE SublogIn(Publish(r, p), canonical, proposals)
<1>1. SublogIn(formal[r], canonical, proposals)
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Sublog, SublogIn
<1>2. SublogIn(Result(p), canonical, proposals)
    BY RecoveryResultIsCanonicalSublog
<1> QED BY <1>1, <1>2 DEF Publish

THEOREM FormalChangesHaveSublogSource ==
    ASSUME ProofInvariant, EntryContextUnique, ProtocolNext, TypeOK'
    PROVE FormalOldOrFullSource
<1>1. formal \in [Replicas -> SUBSET Entries] /\ retained \in [Replicas -> SUBSET proposals]
      /\ (\A r \in Replicas : SublogIn(formal[r], canonical, proposals))
      /\ (FormalAnchorChanges \/ UNCHANGED formal)
    BY FormalAnchorActionProjection DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, CanonicalShape, SublogIn, Sublog
<1>2. ASSUME NEW c \in Replicas, NEW v, CreateEntry(c, v)
      PROVE FormalOldOrFullSource
    <2>1. role'[c] = "Leader" /\ LastTerm(formal'[c]) = term'[c]
          /\ \E p \in proposals' : p.epoch = term'[c] /\ Result(p) \subseteq formal'[c]
        BY EntryCreationHasTermAndAnchor, <1>2
    <2>2. \A r \in Replicas \ {c} : formal'[r] = formal[r]
        BY ONLY SMT, <1>1, <1>2 DEF CreateEntry
    <2> QED BY ONLY ZenonT(5), <1>1, <2>1, <2>2 DEF FormalOldOrFullSource
<1>3. ASSUME NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
      PROVE FormalOldOrFullSource
    <2>1. role'[c] = "Leader" /\ LastTerm(formal'[c]) = term'[c]
          /\ \E p \in proposals' : p.epoch = term'[c] /\ Result(p) \subseteq formal'[c]
        BY SuccessorCreationHasTermAndAnchor, <1>3
    <2>2. \A r \in Replicas \ {c} : formal'[r] = formal[r]
        BY ONLY SMT, <1>1, <1>3 DEF CreateSuccessor
    <2> QED BY ONLY ZenonT(5), <1>1, <2>1, <2>2 DEF FormalOldOrFullSource
<1>4. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
      PROVE FormalOldOrFullSource
    <2>1. SublogIn(formal'[r], canonical, proposals)
        BY ReceiveKeepsCanonicalSublog, <1>4
    <2>2. \A s \in Replicas \ {r} : formal'[s] = formal[s]
        BY ONLY SMT, <1>1, <1>4 DEF ReceiveEntry
    <2> QED BY ONLY ZenonT(5), <1>1, <2>1, <2>2 DEF FormalOldOrFullSource
<1>5. \A c \in Replicas : ConfirmProposal(c) => FormalOldOrFullSource
    BY SMT, PublishedLogIsOldCanonicalSublog, <1>1 DEF ConfirmProposal, FormalOldOrFullSource
<1>6. \A r \in Replicas : \A p : LearnConfirmation(r, p) => FormalOldOrFullSource
    BY SMT, PublishedLogIsOldCanonicalSublog, <1>1 DEF LearnConfirmation, FormalOldOrFullSource
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF FormalOldOrFullSource, FormalAnchorChanges

THEOREM FormalSublogsInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, EntryContextUnique, ProofNext,
           TypeOK', FiniteLogInvariant'
    PROVE FormalSublogs(formal', canonical', proposals')
<1>1. ProtocolNext /\ GhostNext /\ StepFacts /\ term' \in [Replicas -> Terms]
    BY CandidateStepHasMonotonicFacts DEF ProofNext, Next, TypeOK
<1>20. proposals \subseteq proposals'
    BY ProposalsNeverShrink, <1>1
<1>2. proposals \subseteq proposals' /\ \A t \in Terms : canonical[t] \subseteq canonical'[t]
    BY SMT, <1>1, <1>20 DEF GhostNext
<1>3. CanonicalPrefixesPersist(canonical, canonical')
    BY CanonicalPrefixesInductiveStep, <1>1
<1>4. FormalOldOrFullSource /\ PostLeaderEqualsCanonical
    BY FormalChangesHaveSublogSource, LeaderCanonicalEqualityInductiveStep, <1>1
<1>5. \A r \in Replicas : formal'[r] \subseteq Entries /\ IsFiniteSet(formal'[r])
    BY DEF TypeOK, FiniteLogInvariant, FiniteNodeData
<1>6. ASSUME NEW r \in Replicas
      PROVE SublogIn(formal'[r], canonical', proposals')
    <2>1. CASE SublogIn(formal'[r], canonical, proposals)
        BY SublogTransport, <1>2, <1>3, <1>5, <1>6, <2>1
    <2>2. CASE ~SublogIn(formal'[r], canonical, proposals)
        <3>1. role'[r] = "Leader" /\ formal'[r] = canonical'[term'[r]]
              /\ LastTerm(formal'[r]) = term'[r]
              /\ \E p \in proposals' : p.epoch = term'[r] /\ Result(p) \subseteq formal'[r]
            BY <1>4, <1>6, <2>2 DEF FormalOldOrFullSource, PostLeaderEqualsCanonical
        <3> QED BY SMT, <1>1, <1>6, <3>1 DEF SublogIn
    <2> QED BY <2>1, <2>2
<1> QED BY <1>6 DEF FormalSublogs
=============================================================================
