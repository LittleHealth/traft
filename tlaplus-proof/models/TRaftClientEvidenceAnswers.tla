---------------------- MODULE TRaftClientEvidenceAnswers ---------------------
EXTENDS TRaftReadResultAgreement, TRaftClientEvidenceInputs, TRaftPointStoreEvaluation

THEOREM AppliedFirstOccurrenceIsGlobalFirst ==
    ASSUME AppliedEvidencePrefixClosed, AppliedEvidence, TypeOK,
           EvidenceEntries \subseteq Entries, NEW r \in Replicas,
           NEW e \in FirstRequestEntries(applied[r])
    PROVE e \in FirstRequestEntries(EvidenceEntries)
<1>1. e \in applied[r] /\ e \in EvidenceEntries /\ e.kind = "data"
      /\ e.part \in Int
    BY SMT DEF FirstRequestEntries, AppliedEvidence, EvidenceEntries, TypeOK, Entries, Partitions
<1>2. Prefix(EvidenceEntries, e.part - 1) \subseteq applied[r]
    BY <1>1 DEF AppliedEvidencePrefixClosed
<1>3. \A f \in EvidenceEntries : f.part < e.part => f \in applied[r]
    BY SMT, <1>1, <1>2 DEF Prefix, Entries, Partitions
<1> QED BY SMT, <1>1, <1>3 DEF FirstRequestEntries

THEOREM ReadyAnswerMatchesGlobalEvidenceInterpretation ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           AppliedEntriesPreserved, AppliedPrefixClosure, ApplicationMatchesAppliedSet,
           RequestIdentityState,
           \A t \in Terms : PointLog(canonical[t]),
           \A t \in Terms : \A e \in canonical[t] : e.kind = "data" => e.value \in calls,
           \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls,
           NEW r \in Replicas, NEW q \in calls, cache[r][q.id].ready
    PROVE AppliedCache(EvidenceEntries)[q.id] = cache[r][q.id]
<1>1. AppliedEvidencePrefixClosed /\ AppliedEvidence /\ TypeOK
      /\ EvidenceEntries \subseteq Entries /\ PointLog(EvidenceEntries)
      /\ \A e \in EvidenceEntries : e.kind = "data" => e.value \in calls
    BY ApplicationPrefixesContainAllEarlierEvidence, EvidenceEntriesAreFiniteAndTyped,
       EvidenceEntriesRespectPointPartitions, EvidenceDataHasAnActualCall
       DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, HistoryOriginInvariant
<1>2. PICK e \in FirstRequestEntries(applied[r]) :
          e.value = q /\ cache[r][q.id].value =
            IF q.op = "Get" THEN LastWriteValue(PointWritesBefore(applied[r], q.key, e.part)) ELSE "OK"
    BY ReadyCacheNamesItsOriginalAppliedCommand
<1>3. e \in FirstRequestEntries(EvidenceEntries)
    BY AppliedFirstOccurrenceIsGlobalFirst, <1>1, <1>2
<1>4. \A f \in FirstRequestEntries(EvidenceEntries) : f.value.id = q.id => f = e
    BY FirstRequestIdentityIsUnique, <1>1, <1>2, <1>3
<1>5. RequestEntries(EvidenceEntries, q.id) = {e}
      /\ q.id \in RequestIds /\ e.part \in Int
      /\ applied[r] \subseteq Entries /\ e \in applied[r]
    BY SMT, <1>1, <1>2, <1>3, <1>4
       DEF RequestEntries, FirstRequestEntries, RequestIdentityState, ClientCommands,
           Entries, Partitions, TypeOK
<1>6. Prefix(applied[r], e.part - 1) = Prefix(EvidenceEntries, e.part - 1)
    BY AppliedBoundaryPrefixEqualsEvidencePrefix, <1>1, <1>5
<1>7. PointWritesBefore(applied[r], q.key, e.part)
          = PointWritesBefore(EvidenceEntries, q.key, e.part)
    BY EarlierWritesDependOnlyOnEarlierEntries, <1>1, <1>5, <1>6
<1>8. (CHOOSE f \in RequestEntries(EvidenceEntries, q.id) : TRUE) = e
    BY ZenonT(5), <1>5
<1>90. cache[r] = AppliedCache(applied[r])
    BY DEF ApplicationMatchesAppliedSet
<1>900. q.id \in RequestIds
    BY ONLY <1>5
<1>901. AppliedCache(applied[r])[q.id].ready \in BOOLEAN
       /\ AppliedCache(applied[r])[q.id] =
          [ready |-> AppliedCache(applied[r])[q.id].ready,
           value |-> AppliedCache(applied[r])[q.id].value]
    BY ONLY AppliedCacheRecordShape, <1>900, ZenonT(5)
<1>91. cache[r][q.id].ready \in BOOLEAN
       /\ cache[r][q.id] = [ready |-> cache[r][q.id].ready, value |-> cache[r][q.id].value]
    BY ONLY <1>90, <1>901
<1>9. cache[r][q.id] = [ready |-> TRUE, value |-> cache[r][q.id].value]
    BY <1>91
<1>10. AppliedCache(EvidenceEntries)[q.id] = [ready |-> TRUE, value |->
              IF e.value.op = "Get"
              THEN LastWriteValue(PointWritesBefore(EvidenceEntries, e.value.key, e.part)) ELSE "OK"]
    BY AppliedCacheAtPresentIdentity, <1>5, <1>8
<1> QED BY ONLY <1>2, <1>7, <1>9, <1>10
=============================================================================
