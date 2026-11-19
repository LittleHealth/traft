----------------------- MODULE TRaftBoundedObserverStep ----------------------
EXTENDS TRaftBoundedMappingAliases, TRaftBoundedProtocolRefinement

THEOREM BoundedObservationImplementsExpandedObservation ==
    ASSUME MaxTerm \in Nat \ {0}, ObserverMappingContext', Observe
    PROVE ExpandedObservation
<1>1. ObservationEquations /\ ObservationBooleans
    BY ObserveHasEquations
<1>2. Evidence(ackMessages') = Infinite!Evidence(ackMessages')
    BY BoundedAcksHaveTheSameUnboundedEvidence DEF ObserverMappingContext
<1>3. EpochClosure(partitionHistory') = EpochClosure(partitionHistory) \cup
          CertifiedClosed(UnboundedClosed', commitHistory', Nat \ {0})
    BY BoundedPartitionHistoryGrowthEmbeds DEF ObserverMappingContext
<1> QED BY <1>1, <1>2, <1>3 DEF ObservationEquations, ExpandedObservation

THEOREM BoundedObservedStepRefinesUnbounded ==
    ASSUME MaxTerm \in Nat \ {0}, ObserverMappingContext', Next
    PROVE MappedCore!Next
<1>1. Infinite!ProtocolNext
    BY BoundedProtocolStepEmbeds DEF Next
<1>2. ExpandedObservation
    BY BoundedObservationImplementsExpandedObservation DEF Next
<1> QED BY PhysicalActionsIgnorePartitionHistoryMapping, MappedObservationIdentity,
           <1>1, <1>2 DEF MappedCore!Next
=============================================================================
