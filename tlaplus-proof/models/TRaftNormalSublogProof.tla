------------------------- MODULE TRaftNormalSublogProof ----------------------
EXTENDS TRaftSublogSupport, TRaftCreatedEntryProof

\* TypeOK' is established independently by TypeOKInductiveStep before
\* CanonicalShapeInductiveStep calls this layer. No post-state Safety,
\* sublog, or recovery-preservation premise is assumed.

THEOREM NormalCreatedLogHasTermAndAnchor ==
    ASSUME ProofInvariant, TypeOK', NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE role'[c] = "Leader" /\ LastTerm(formal'[c]) = term'[c]
          /\ \E p \in proposals' : p.epoch = term'[c] /\ Result(p) \subseteq formal'[c]
<1>1. formal \in [Replicas -> SUBSET Entries] /\ IsFiniteSet(formal[c])
      /\ term[c] \in Terms /\ Sublog(formal[c])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape,
       FiniteLogInvariant, FiniteNodeData
<1>2. Aligned(c, term[c]) /\ role'[c] = "Leader" /\ term'[c] = term[c]
      /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, v, k, successor)} /\ UNCHANGED proposals
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, NormalCreatedEntry
<1>30. formal' \in [Replicas -> SUBSET Entries]
    BY DEF TypeOK
<1>3. NormalCreatedEntry(c, v, k, successor) \in Entries
      /\ NormalCreatedEntry(c, v, k, successor).index = LastIndex(formal[c]) + 1
      /\ NormalCreatedEntry(c, v, k, successor).term = term[c]
    BY SMT, <1>2, <1>30 DEF NormalCreatedEntry, Entry
<1>4. LastIndex(formal[c]) \in Nat
      /\ \A e \in formal[c] : e.index \in Nat /\ e.index <= LastIndex(formal[c])
    BY FiniteLogNumericFrontier, <1>1
<1>5. \A e \in formal[c] : e.index < NormalCreatedEntry(c, v, k, successor).index
    BY ONLY SMT, <1>4 DEF NormalCreatedEntry, Entry
<1>50. formal[c] \subseteq Entries
    BY <1>1
<1>60. LastTerm(formal[c] \cup {NormalCreatedEntry(c, v, k, successor)})
            = NormalCreatedEntry(c, v, k, successor).term
    BY ONLY NewGreatestEntryDeterminesLastTerm, <1>50, <1>3, <1>5, IsaM("blast")
<1>6. LastTerm(formal'[c]) = term'[c]
    BY ONLY <1>2, <1>3, <1>60
<1>7. formal[c] # {} /\ LastTerm(formal[c]) = term[c]
    BY AlignmentIdentifiesSublogEpoch, <1>1, <1>2
<1>8. \E p \in proposals : p.epoch = term[c] /\ Result(p) \subseteq formal[c]
    BY <1>1, <1>7 DEF Sublog
<1> QED BY ONLY ZenonT(5), <1>2, <1>6, <1>8

THEOREM EntryCreationHasTermAndAnchor ==
    ASSUME ProofInvariant, TypeOK', NEW c \in Replicas, NEW v, CreateEntry(c, v)
    PROVE role'[c] = "Leader" /\ LastTerm(formal'[c]) = term'[c]
          /\ \E p \in proposals' : p.epoch = term'[c] /\ Result(p) \subseteq formal'[c]
<1>1. formal \in [Replicas -> SUBSET Entries] /\ IsFiniteSet(formal[c])
      /\ term[c] \in Terms /\ Sublog(formal[c])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape,
       FiniteLogInvariant, FiniteNodeData
<1>2. Aligned(c, term[c]) /\ role'[c] = "Leader" /\ term'[c] = term[c]
      /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, v, "data", FALSE)} /\ UNCHANGED proposals
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, NormalCreatedEntry
<1>30. formal' \in [Replicas -> SUBSET Entries]
    BY DEF TypeOK
<1>3. NormalCreatedEntry(c, v, "data", FALSE) \in Entries
      /\ NormalCreatedEntry(c, v, "data", FALSE).index = LastIndex(formal[c]) + 1
      /\ NormalCreatedEntry(c, v, "data", FALSE).term = term[c]
    BY SMT, <1>2, <1>30 DEF NormalCreatedEntry, Entry
<1>4. LastIndex(formal[c]) \in Nat
      /\ \A e \in formal[c] : e.index \in Nat /\ e.index <= LastIndex(formal[c])
    BY FiniteLogNumericFrontier, <1>1
<1>5. \A e \in formal[c] : e.index < NormalCreatedEntry(c, v, "data", FALSE).index
    BY ONLY SMT, <1>4 DEF NormalCreatedEntry, Entry
<1>50. formal[c] \subseteq Entries
    BY <1>1
<1>60. LastTerm(formal[c] \cup {NormalCreatedEntry(c, v, "data", FALSE)})
            = NormalCreatedEntry(c, v, "data", FALSE).term
    BY ONLY NewGreatestEntryDeterminesLastTerm, <1>50, <1>3, <1>5, IsaM("blast")
<1>6. LastTerm(formal'[c]) = term'[c]
    BY ONLY <1>2, <1>3, <1>60
<1>7. formal[c] # {} /\ LastTerm(formal[c]) = term[c]
    BY AlignmentIdentifiesSublogEpoch, <1>1, <1>2
<1>8. \E p \in proposals : p.epoch = term[c] /\ Result(p) \subseteq formal[c]
    BY <1>1, <1>7 DEF Sublog
<1> QED BY ONLY ZenonT(5), <1>2, <1>6, <1>8


THEOREM SuccessorCreationHasTermAndAnchor ==
    ASSUME ProofInvariant, TypeOK', NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
    PROVE role'[c] = "Leader" /\ LastTerm(formal'[c]) = term'[c]
          /\ \E p \in proposals' : p.epoch = term'[c] /\ Result(p) \subseteq formal'[c]
<1>1. formal \in [Replicas -> SUBSET Entries] /\ IsFiniteSet(formal[c])
      /\ term[c] \in Terms /\ Sublog(formal[c])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape,
       FiniteLogInvariant, FiniteNodeData
<1>2. Aligned(c, term[c]) /\ role'[c] = "Leader" /\ term'[c] = term[c]
      /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, v, k, TRUE)} /\ UNCHANGED proposals
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, NormalCreatedEntry
<1>30. formal' \in [Replicas -> SUBSET Entries]
    BY DEF TypeOK
<1>3. NormalCreatedEntry(c, v, k, TRUE) \in Entries
      /\ NormalCreatedEntry(c, v, k, TRUE).index = LastIndex(formal[c]) + 1
      /\ NormalCreatedEntry(c, v, k, TRUE).term = term[c]
    BY SMT, <1>2, <1>30 DEF NormalCreatedEntry, Entry
<1>4. LastIndex(formal[c]) \in Nat
      /\ \A e \in formal[c] : e.index \in Nat /\ e.index <= LastIndex(formal[c])
    BY FiniteLogNumericFrontier, <1>1
<1>5. \A e \in formal[c] : e.index < NormalCreatedEntry(c, v, k, TRUE).index
    BY ONLY SMT, <1>4 DEF NormalCreatedEntry, Entry
<1>50. formal[c] \subseteq Entries
    BY <1>1
<1>60. LastTerm(formal[c] \cup {NormalCreatedEntry(c, v, k, TRUE)})
            = NormalCreatedEntry(c, v, k, TRUE).term
    BY ONLY NewGreatestEntryDeterminesLastTerm, <1>50, <1>3, <1>5, IsaM("blast")
<1>6. LastTerm(formal'[c]) = term'[c]
    BY ONLY <1>2, <1>3, <1>60
<1>7. formal[c] # {} /\ LastTerm(formal[c]) = term[c]
    BY AlignmentIdentifiesSublogEpoch, <1>1, <1>2
<1>8. \E p \in proposals : p.epoch = term[c] /\ Result(p) \subseteq formal[c]
    BY <1>1, <1>7 DEF Sublog
<1> QED BY ONLY ZenonT(5), <1>2, <1>6, <1>8

=============================================================================
