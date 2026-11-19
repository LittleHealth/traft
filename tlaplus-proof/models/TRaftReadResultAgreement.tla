----------------------- MODULE TRaftReadResultAgreement ----------------------
EXTENDS TRaftPointStoreEvaluation, TRaftAppliedEvidencePrefix

ReadyResultsAgree == \A r, s \in Replicas : \A q \in calls :
    (cache[r][q.id].ready /\ cache[s][q.id].ready) => cache[r][q.id].value = cache[s][q.id].value

THEOREM FirstAppliedOccurrencesHaveSamePartition ==
    ASSUME AppliedEvidencePrefixClosed, AppliedEvidence, TypeOK,
           NEW r \in Replicas, NEW s \in Replicas,
           NEW e \in FirstRequestEntries(applied[r]), NEW f \in FirstRequestEntries(applied[s]),
           e.value.id = f.value.id
    PROVE e.part = f.part
<1>1. e \in applied[r] /\ f \in applied[s] /\ e.kind = "data" /\ f.kind = "data"
      /\ e.part \in Int /\ f.part \in Int
    BY SMT DEF FirstRequestEntries, TypeOK, Entries, Partitions
<1>2. e \in EvidenceEntries /\ f \in EvidenceEntries
    BY SMT, <1>1 DEF AppliedEvidence, EvidenceEntries
<1>3. ASSUME e.part < f.part
      PROVE FALSE
    <2>1. e \in Prefix(EvidenceEntries, f.part - 1)
        BY ONLY SMT, <1>1, <1>2, <1>3 DEF Prefix
    <2>2. e \in applied[s]
        BY <1>1, <2>1 DEF AppliedEvidencePrefixClosed
    <2> QED BY <1>1, <1>3, <2>2 DEF FirstRequestEntries
<1>4. ASSUME f.part < e.part
      PROVE FALSE
    <2>1. f \in Prefix(EvidenceEntries, e.part - 1)
        BY ONLY SMT, <1>1, <1>2, <1>4 DEF Prefix
    <2>2. f \in applied[r]
        BY <1>1, <2>1 DEF AppliedEvidencePrefixClosed
    <2> QED BY <1>1, <1>4, <2>2 DEF FirstRequestEntries
<1> QED BY ONLY SMT, <1>1, <1>3, <1>4

THEOREM ReadyCacheNamesItsOriginalAppliedCommand ==
    ASSUME ApplicationMatchesAppliedSet, RequestIdentityState, AppliedEntriesPreserved,
           \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls,
           NEW r \in Replicas, NEW q \in calls, cache[r][q.id].ready
    PROVE \E e \in FirstRequestEntries(applied[r]) :
        /\ e.value = q
        /\ cache[r][q.id].value =
              IF q.op = "Get" THEN LastWriteValue(PointWritesBefore(applied[r], q.key, e.part)) ELSE "OK"
<1>1. q.id \in RequestIds /\ cache[r] = AppliedCache(applied[r])
    BY DEF RequestIdentityState, ClientCommands, ApplicationMatchesAppliedSet
<1>2. RequestEntries(applied[r], q.id) # {}
    BY SMT, <1>1 DEF AppliedCache
<1>3. DEFINE e == CHOOSE f \in RequestEntries(applied[r], q.id) : TRUE
<1>4. e \in FirstRequestEntries(applied[r]) /\ e.value.id = q.id
      /\ e \in applied[r] /\ e.kind = "data"
    BY ZenonT(5), <1>2 DEF e, RequestEntries, FirstRequestEntries
<1>5. e.value \in calls /\ e.value = q
    BY <1>4 DEF AppliedEntriesPreserved, RequestIdentityState
<1>6. cache[r][q.id].value =
          IF q.op = "Get" THEN LastWriteValue(PointWritesBefore(applied[r], q.key, e.part)) ELSE "OK"
    <2>1. AppliedCache(applied[r])[q.id] = [ready |-> TRUE, value |->
              IF e.value.op = "Get"
              THEN LastWriteValue(PointWritesBefore(applied[r], e.value.key, e.part)) ELSE "OK"]
        BY AppliedCacheAtPresentIdentity, <1>1, <1>2 DEF e
    <2> QED BY ONLY <1>1, <1>5, <2>1
<1> QED BY <1>4, <1>5, <1>6

THEOREM CandidateReadyResultsAgree ==
    ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique,
           AppliedEntriesPreserved, AppliedPrefixClosure, RequestIdentityState,
           ApplicationMatchesAppliedSet,
           \A r \in Replicas : \A e \in formal[r] : e.kind = "data" => e.value \in calls
    PROVE ReadyResultsAgree
<1>1. AppliedEvidencePrefixClosed /\ AppliedEvidence /\ TypeOK
    BY ApplicationPrefixesContainAllEarlierEvidence
       DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, HistoryOriginInvariant
<1>2. ASSUME NEW r \in Replicas, NEW s \in Replicas, NEW q \in calls,
            cache[r][q.id].ready, cache[s][q.id].ready
      PROVE cache[r][q.id].value = cache[s][q.id].value
    <2>1. PICK e \in FirstRequestEntries(applied[r]) : e.value = q
              /\ cache[r][q.id].value = IF q.op = "Get"
                     THEN LastWriteValue(PointWritesBefore(applied[r], q.key, e.part)) ELSE "OK"
        BY ReadyCacheNamesItsOriginalAppliedCommand, <1>2
    <2>2. PICK f \in FirstRequestEntries(applied[s]) : f.value = q
              /\ cache[s][q.id].value = IF q.op = "Get"
                     THEN LastWriteValue(PointWritesBefore(applied[s], q.key, f.part)) ELSE "OK"
        BY ReadyCacheNamesItsOriginalAppliedCommand, <1>2
    <2>3. e.part = f.part
        BY FirstAppliedOccurrencesHaveSamePartition, <1>1, <1>2, <2>1, <2>2
    <2>4. applied[r] \subseteq Entries /\ applied[s] \subseteq Entries /\ e.part \in Int
          /\ e \in applied[r] /\ f \in applied[s]
        BY SMT, <1>1, <1>2, <2>1, <2>2 DEF TypeOK, FirstRequestEntries, Entries, Partitions
    <2>5. Prefix(applied[r], e.part - 1) = Prefix(applied[s], e.part - 1)
        BY AppliedBoundaryPrefixEqualsEvidencePrefix, <1>1, <1>2, <2>3, <2>4
    <2>6. PointWritesBefore(applied[r], q.key, e.part)
              = PointWrites(Prefix(applied[r], e.part - 1), q.key)
          /\ PointWritesBefore(applied[s], q.key, e.part)
              = PointWrites(Prefix(applied[s], e.part - 1), q.key)
        BY EarlierWritesDependOnlyOnEarlierEntries, <2>4
    <2> QED BY ONLY <2>1, <2>2, <2>3, <2>5, <2>6
<1> QED BY <1>2 DEF ReadyResultsAgree
=============================================================================
