---------------------- MODULE TRaftApplicationPrefixProof --------------------
EXTENDS TRaftProofState, TRaftApplicationOrderProof, TRaftLogContextState

\* Application facts only: none of these predicates enables a protocol step.
PrefixClosed(A, L) == \A e \in A : Prefix(L, e.part - 1) \subseteq A
AppliedPrefixClosure == \A r \in Replicas : PrefixClosed(applied[r], formal[r])
UniqueLogContexts(E) == \A a, b \in E : a.entry = b.entry => a.prefix = b.prefix

THEOREM SharedEntryKeepsItsPrefix ==
    ASSUME NEW L, NEW M, NEW E, NEW F, LogContexts(L, E), LogContexts(M, F),
           E \subseteq F, UniqueLogContexts(F), NEW e \in L \cap M
    PROVE Prefix(L, e.part - 1) = Prefix(M, e.part - 1)
<1>1. PICK a \in E : a.entry = e /\ a.prefix = Prefix(L, e.part - 1)
    BY DEF LogContexts
<1>2. PICK b \in F : b.entry = e /\ b.prefix = Prefix(M, e.part - 1)
    BY DEF LogContexts
<1>3. a \in F /\ b \in F /\ a.entry = b.entry
    BY <1>1, <1>2
<1> QED BY <1>1, <1>2, <1>3 DEF UniqueLogContexts

THEOREM PrefixClosureSurvivesLogReplacement ==
    ASSUME NEW A, NEW L, NEW M, NEW E, NEW F,
           A \subseteq L, A \subseteq M, PrefixClosed(A, L),
           LogContexts(L, E), LogContexts(M, F), E \subseteq F, UniqueLogContexts(F)
    PROVE PrefixClosed(A, M)
<1>1. \A e \in A : Prefix(L, e.part - 1) = Prefix(M, e.part - 1)
    BY SharedEntryKeepsItsPrefix
<1> QED BY <1>1 DEF PrefixClosed

THEOREM ApplyingOneEntryPreservesPrefixClosure ==
    ASSUME AppliedPrefixClosure, AppliedShape, NEW r \in Replicas, NEW e, ApplyEntry(r, e)
    PROVE AppliedPrefixClosure'
<1>1. UNCHANGED formal /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]
      /\ applied' = [applied EXCEPT ![r] = @ \cup {e}]
    BY DEF ApplyEntry
<1>2. applied'[r] = applied[r] \cup {e}
      /\ \A s \in Replicas \ {r} : applied'[s] = applied[s]
    BY SMT, <1>1 DEF AppliedShape
<1>3. PrefixClosed(applied'[r], formal'[r])
    BY SMT, <1>1, <1>2 DEF AppliedPrefixClosure, PrefixClosed
<1>4. \A s \in Replicas \ {r} : PrefixClosed(applied'[s], formal'[s])
    BY <1>1, <1>2 DEF AppliedPrefixClosure
<1> QED BY SMT, <1>3, <1>4 DEF AppliedPrefixClosure

THEOREM AppliedPrefixClosureInitially == Init => AppliedPrefixClosure
BY DEF Init, AppliedPrefixClosure, PrefixClosed

THEOREM AppliedPrefixClosureInductiveStep ==
    ASSUME AppliedPrefixClosure, ProofInvariant, Next, ProofInvariant',
           AppliedEntriesPreserved, AppliedEntriesPreserved', EntryContextUnique'
    PROVE AppliedPrefixClosure'
<1>1. TypeOK /\ CanonicalShape /\ CanonicalShape'
      /\ entryContexts \subseteq entryContexts' /\ UniqueLogContexts(entryContexts')
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       Next, Observe, EntryContextUnique, UniqueLogContexts
<1>2. AppliedShape /\ ((\E r \in Replicas : \E e : ApplyEntry(r, e)) \/ UNCHANGED applied)
    BY SMT, OnlyApplyChangesApplied, <1>1 DEF TypeOK, AppliedShape, Next
<1>3. CASE \E r \in Replicas : \E e : ApplyEntry(r, e)
    BY ApplyingOneEntryPreservesPrefixClosure, <1>2, <1>3
<1>4. CASE UNCHANGED applied
    <2>1. ASSUME NEW r \in Replicas
          PROVE PrefixClosed(applied'[r], formal'[r])
        <3>1. applied[r] \subseteq formal[r] /\ applied[r] \subseteq formal'[r]
              /\ PrefixClosed(applied[r], formal[r])
            BY <1>4, <2>1 DEF AppliedEntriesPreserved, AppliedPrefixClosure
        <3>2. LogContexts(formal[r], entryContexts)
              /\ LogContexts(formal'[r], entryContexts')
            BY <1>1, <2>1 DEF CanonicalShape, ContextSound, LogContexts
        <3> QED BY PrefixClosureSurvivesLogReplacement, <1>1, <1>4, <3>1, <3>2
    <2> QED BY <2>1 DEF AppliedPrefixClosure
<1> QED BY <1>2, <1>3, <1>4

THEOREM NewApplicationDoesNotGoBackwards ==
    ASSUME AppliedPrefixClosure, AppliedEntriesPreserved, TypeOK,
           NEW r \in Replicas, NEW e, ApplyEntry(r, e)
    PROVE \A x \in applied[r] : x.part <= e.part
<1>1. e \in formal[r] /\ e \notin applied[r]
      /\ applied[r] \subseteq formal[r] /\ formal[r] \subseteq Entries
    BY DEF ApplyEntry, AppliedEntriesPreserved, TypeOK
<1>2. e.part \in Int /\ \A x \in applied[r] : x.part \in Int
    BY SMT, <1>1 DEF Entries, Partitions
<1>3. ASSUME NEW x \in applied[r]
      PROVE x.part <= e.part
    <2>1. Prefix(formal[r], x.part - 1) \subseteq applied[r]
        BY <1>3 DEF AppliedPrefixClosure, PrefixClosed
    <2> QED BY ONLY SMT, <1>1, <1>2, <1>3, <2>1 DEF Prefix
<1> QED BY <1>3
=============================================================================
