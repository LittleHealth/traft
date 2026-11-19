-------------------- MODULE TRaftBoundedObserverRefinement -------------------
EXTENDS TRaftBoundedObserverStep, TRaftProtocolSafety

THEOREM ProtocolEstablishesObserverMappingContext ==
    Spec => []ObserverMappingContext
<1>1. Spec => []LiftedSafety!Inv
    BY ProtocolInvariant
<1>2. LiftedSafety!Inv => ObserverMappingContext
    BY LiftedSafetyPredicateIdentity
       DEF LiftedSafety!Inv, Safety, TypeOK, LiftedSafety!ProofInvariant,
       LiftedSafety!PreProvenanceInvariant, LiftedSafety!RecoveryInvariant,
       LiftedSafety!AckOrigin, LiftedSafety!Terms, Terms, ObserverMappingContext
<1> QED BY PTL, <1>1, <1>2

\* The refinement leaves all protocol variables unchanged and maps the
\* partition-history observer by upward authorization-epoch closure.
\* Its premises come from the separately checked protocol induction.
THEOREM UnboundedCoreRefinement ==
    ASSUME MaxTerm \in Nat \ {0}, Absent \notin Infinite!ProposalRecords
    PROVE Spec => (MappedCore!ParameterAssumptions /\ MappedCore!SentinelSeparation /\ MappedCore!Spec)
<1>0. MappedCore!ParameterAssumptions /\ MappedCore!SentinelSeparation
    BY BoundedParametersAdmitUnboundedCore
<1>1. Init => MappedCore!Init
    BY InitialPartitionHistoryMapping
<1>2. ObserverMappingContext' /\ [Next]_vars => [MappedCore!Next]_MappedCore!vars
    BY BoundedObservedStepRefinesUnbounded, UnchangedStateHasUnchangedMappedState
<1>3. Spec => []ObserverMappingContext
    BY ProtocolEstablishesObserverMappingContext
<1> QED BY PTL, <1>0, <1>1, <1>2, <1>3 DEF Spec, MappedCore!Spec
=============================================================================
