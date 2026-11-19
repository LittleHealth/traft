----------------------- MODULE TRaftApplicationScenarios ---------------------
EXTENDS TRaftClientScenarios, TRaftPointStoreState

AppliedPrefixCheck == \A r \in Replicas : \A e \in applied[r] :
    Prefix(formal[r], e.part - 1) \subseteq applied[r]
ReadyCacheAgreementCheck == \A r, s \in Replicas : \A q \in calls :
    (cache[r][q.id].ready /\ cache[s][q.id].ready) => cache[r][q.id].value = cache[s][q.id].value
ReadyCacheOriginCheck == \A r \in Replicas : \A id \in RequestIds :
    cache[r][id].ready <=> \E e \in applied[r] : e.kind = "data" /\ e.value.id = id
=============================================================================
