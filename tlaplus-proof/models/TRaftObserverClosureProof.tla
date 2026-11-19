---------------------- MODULE TRaftObserverClosureProof ----------------------
EXTENDS TRaftCore, TLAPS

PresentWinners == {[node |-> r, epoch |-> term[r]] :
    r \in {x \in Replicas : role[x] = "LeaderCandidate"}}
PresentViews == {[node |-> r, epoch |-> term[r], entries |-> formal[r]] :
    r \in {x \in Replicas : role[x] = "Leader"}}
PresentContexts ==
    (UNION { {[entry |-> e, prefix |-> Prefix(formal[r], e.part - 1)] :
                 e \in {x \in formal[r] : x.term = term[r]}} :
                r \in {n \in Replicas : role[n] = "Leader"}}) \cup
    {[entry |-> p.first, prefix |-> p.prefix] : p \in proposals}
PresentClosed == (UNION {
    {[epoch |-> term[r], part |-> q, entries |-> Part(formal[r], q)] :
         q \in {j \in Partitions : j < Cur(formal[r]) /\ Part(formal[r], j) # {}}} :
    r \in Replicas})
PresentPartitions == (UNION {
    {[epoch |-> t, part |-> v.part, entries |-> v.entries] :
        t \in {u \in Terms \ {0} : u >= v.epoch /\
             \A e \in v.entries : \E f \in commitHistory : f.entry = e /\ f.epoch <= u}} :
    v \in PresentClosed})
PresentAppliedPartitions == (UNION {
    {[node |-> r, part |-> q, entries |-> Part(formal[r], q)] :
        q \in {j \in 0..(Cur(formal[r]) - 1) : Part(formal[r], j) # {}
                   /\ Part(formal[r], j) \subseteq applied[r]}} : r \in Replicas})

ObserverBooleanTypes == applicationOrderOK \in BOOLEAN /\ appendOnlyOK \in BOOLEAN
ObserverClosure ==
    /\ ObserverBooleanTypes
    /\ PresentWinners \subseteq winners
    /\ PresentViews \subseteq leaderViews
    /\ PresentContexts \subseteq entryContexts
    /\ Evidence(ackMessages) \subseteq commitHistory
    /\ PresentPartitions \subseteq partitionHistory
    /\ PresentAppliedPartitions \subseteq appliedPartitionHistory

THEOREM ObserversInitiallyClosed == Init => ObserverClosure
BY SMT DEF Init, ObserverClosure, ObserverBooleanTypes, PresentWinners, PresentViews, PresentContexts,
    PresentClosed, PresentPartitions, PresentAppliedPartitions, Evidence, Cur, MaxOr, Part

ObservationEquations ==
    /\ winners' = winners \cup PresentWinners'
    /\ leaderViews' = leaderViews \cup PresentViews'
    /\ entryContexts' = entryContexts \cup PresentContexts'
    /\ commitHistory' = commitHistory \cup Evidence(ackMessages')
    /\ partitionHistory' = partitionHistory \cup PresentPartitions'
    /\ appliedPartitionHistory' = appliedPartitionHistory \cup PresentAppliedPartitions'
ObservationBooleans ==
    /\ applicationOrderOK' = (applicationOrderOK /\
         (\A r \in Replicas :
             /\ applied[r] \subseteq applied'[r]
             /\ \A e \in applied'[r] \ applied[r] :
                  /\ e \in formal[r] \cap knownCommitted[r]
                  /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]))
    /\ appendOnlyOK' =
         (appendOnlyOK /\ \A r \in Replicas :
            (role[r] = "Leader" /\ role'[r] = "Leader" /\ term[r] = term'[r])
            => formal[r] \subseteq formal'[r])

THEOREM ObserveHasEquations == Observe => ObservationEquations /\ ObservationBooleans
BY DEF Observe, ObservationEquations, ObservationBooleans, PresentWinners, PresentViews,
    PresentContexts, PresentClosed, PresentPartitions, PresentAppliedPartitions

THEOREM ObservationEstablishesClosure == Observe => ObserverClosure'
<1>0. SUFFICES ASSUME Observe PROVE ObserverClosure'
    OBVIOUS
<1>1. ObservationEquations /\ ObservationBooleans
    BY ObserveHasEquations, <1>0
<1>2. ObserverBooleanTypes'
    BY ONLY SMT, <1>1 DEF ObserverBooleanTypes, ObservationBooleans
<1>3. /\ PresentWinners' \subseteq winners'
      /\ PresentViews' \subseteq leaderViews'
      /\ PresentContexts' \subseteq entryContexts'
      /\ Evidence(ackMessages') \subseteq commitHistory'
      /\ PresentPartitions' \subseteq partitionHistory'
      /\ PresentAppliedPartitions' \subseteq appliedPartitionHistory'
    BY ONLY SMT, <1>1 DEF ObservationEquations
<1> QED BY <1>2, <1>3 DEF ObserverClosure

THEOREM PresentSourcesStutter ==
    ASSUME UNCHANGED protocolVars
    PROVE UNCHANGED <<PresentWinners, PresentViews, PresentContexts, Evidence(ackMessages)>>
<1>0. UNCHANGED <<role, term, formal, proposals, ackMessages>>
    BY DEF protocolVars
<1>1. UNCHANGED PresentWinners
    BY ONLY SMT, <1>0 DEF PresentWinners
<1>2. UNCHANGED PresentViews
    BY ONLY SMT, <1>0 DEF PresentViews
<1>3. UNCHANGED PresentContexts
    <2>1. role' = role /\ term' = term /\ formal' = formal /\ proposals' = proposals
        BY ONLY <1>0
    <2> QED BY ONLY IsaM("auto"), <2>1 DEF PresentContexts
<1>4. UNCHANGED Evidence(ackMessages)
    BY ONLY SMT, <1>0
<1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM PresentPartitionsStutter ==
    ASSUME UNCHANGED <<protocolVars, commitHistory>>
    PROVE UNCHANGED <<PresentPartitions, PresentAppliedPartitions>>
<1>0. UNCHANGED <<term, formal, applied, commitHistory>>
    BY DEF protocolVars
<1>1. UNCHANGED PresentClosed
    BY ONLY SMT, <1>0 DEF PresentClosed
<1>2. UNCHANGED PresentPartitions
    <2>1. commitHistory' = commitHistory /\ PresentClosed' = PresentClosed
        BY ONLY <1>0, <1>1
    <2> QED BY ONLY IsaM("auto"), <2>1 DEF PresentPartitions
<1>3. UNCHANGED PresentAppliedPartitions
    BY ONLY SMT, <1>0 DEF PresentAppliedPartitions
<1> QED BY <1>2, <1>3

THEOREM ClosedObservationStutters ==
    ASSUME ObserverClosure, UNCHANGED protocolVars, Observe
    PROVE UNCHANGED observerVars
<1>0. ObservationEquations /\ ObservationBooleans /\ ObserverClosure
    BY ObserveHasEquations
<1>01. UNCHANGED protocolVars
    OBVIOUS
<1>1. UNCHANGED <<PresentWinners, PresentViews, PresentContexts, Evidence(ackMessages)>>
    BY PresentSourcesStutter
<1>2. UNCHANGED <<winners, leaderViews, entryContexts, commitHistory>>
    <2>1. winners' = winners /\ leaderViews' = leaderViews
          /\ entryContexts' = entryContexts /\ commitHistory' = commitHistory
        BY ONLY IsaM("auto"), <1>0, <1>1 DEF ObserverClosure, ObservationEquations
    <2> QED BY <2>1
<1>3. UNCHANGED <<PresentPartitions, PresentAppliedPartitions>>
    BY PresentPartitionsStutter, <1>2
<1>4. UNCHANGED <<partitionHistory, appliedPartitionHistory>>
    <2>1. partitionHistory' = partitionHistory
          /\ appliedPartitionHistory' = appliedPartitionHistory
        BY ONLY IsaM("auto"), <1>0, <1>3 DEF ObserverClosure, ObservationEquations
    <2> QED BY <2>1
<1>5. UNCHANGED <<applicationOrderOK, appendOnlyOK>>
    <2>1. UNCHANGED <<role, term, formal, applied>>
        BY <1>01 DEF protocolVars
    <2>2. ObserverBooleanTypes /\ ObservationBooleans
        BY <1>0 DEF ObserverClosure
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF ObservationBooleans, ObserverBooleanTypes
<1> QED BY <1>2, <1>4, <1>5 DEF observerVars

THEOREM ObserverClosureStuttering ==
    ASSUME ObserverClosure, UNCHANGED vars
    PROVE ObserverClosure'
<1>1. UNCHANGED <<PresentWinners, PresentViews, PresentContexts, Evidence(ackMessages),
                  PresentPartitions, PresentAppliedPartitions>>
    BY SMT, PresentSourcesStutter, PresentPartitionsStutter DEF vars, observerVars
<1>2. UNCHANGED observerVars /\ ObserverClosure
    BY DEF vars
<1> QED BY ONLY SMT, <1>1, <1>2 DEF ObserverClosure, ObserverBooleanTypes, observerVars
=============================================================================
