---------------------- MODULE TRaftClientPartitionTemporal ----------------------
EXTENDS TRaftPointLiftInvariant, TRaftProtocolSafety

\* Proof-only instance sharing and transport; no protocol guard or premise.

THEOREM ClientProposalsNeverShrink == ClientAction => proposals \subseteq proposals'
<1>1. ClientAction =>
          (\E c \in Replicas : \E selected : BuildRecovery(c, selected)) \/ UNCHANGED proposals
    BY OnlyClientRecoveryCreatesProposal
<1>2. \A c, selected : BuildRecovery(c, selected) => proposals \subseteq proposals'
    BY DEF BuildRecovery
<1> QED BY SMT, <1>1, <1>2

THEOREM ClientObservationLiftsCanonical ==
    ASSUME ClientAction, Observe
    PROVE PointLift!GhostNext
<1>1. proposals \subseteq proposals'
    BY ClientProposalsNeverShrink
<1> QED BY DerivedCanonicalFollowsObserver, <1>1
       DEF PointLift!GhostNext, ProposedAt, PointLift!Terms, Terms, PointLift!Result, Result

THEOREM ClientPointLogsInitially == ClientInit => DerivedPointLogs
<1>1. ASSUME ClientInit
      PROVE DerivedPointLogs
    <2>1. Init /\ DerivedCanonical = [t \in Terms |-> {}]
        BY CoreInitializationLifts, <1>1 DEF ClientInit, LiftedInit
    <2> QED BY SMT, EmptyPointLog, <2>1 DEF DerivedPointLogs, CanonicalPointLogs
<1> QED BY <1>1

THEOREM ClientPointLogsStep ==
    ASSUME DerivedPointLogs, LiftedSafety!Inv, RequestIdentityState,
           ClientAction, Observe, TypeOK'
    PROVE DerivedPointLogs'
<1>1. PointLift!ProofInvariant /\ ElectionSafety /\ term' \in [Replicas -> Terms]
    BY PointLiftStateIdentities, LiftedSafetyPredicateIdentity
       DEF LiftedSafety!Inv, Safety, TypeOK
<1>2. PointLift!GhostNext
    BY ClientObservationLiftsCanonical
<1> QED BY PointLift!ClientPointLogInductiveStep, PointLiftParameters,
       PointLiftInterfaceIdentities, <1>1, <1>2
       DEF DerivedPointLogs, PointLift!ParameterAssumptions,
           PointLift!SentinelSeparation, PointLift!ClientParameters

THEOREM DerivedPointLogsStuttering ==
    ASSUME DerivedPointLogs, UNCHANGED clientVars
    PROVE DerivedPointLogs'
BY SMT DEF clientVars, vars, protocolVars, observerVars,
       DerivedPointLogs, DerivedCanonical

THEOREM ClientPointLogsAlways ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []DerivedPointLogs
<1>1. ClientSpecification(Extra) => []LiftedSafety!Inv /\ []RequestIdentityState /\ []TypeOK
    BY PTL, ClientTemporalRefinement, ProtocolInvariant, ProtocolSafety,
       ClientRequestIdentityAlways DEF Safety
<1>2. ClientInit => DerivedPointLogs
    BY ClientPointLogsInitially
<1>3. DerivedPointLogs /\ LiftedSafety!Inv /\ RequestIdentityState /\ TypeOK'
      /\ [ClientAction /\ Observe /\ Extra]_clientVars => DerivedPointLogs'
    BY ClientPointLogsStep, DerivedPointLogsStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification

THEOREM ClientPartitionIndependence ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => [](ReadIsolation /\ PartitionCommandsIndependent)
<1>1. ClientSpecification(Extra) => []DerivedPointLogs /\ []LiftedSafety!Inv
    BY PTL, ClientPointLogsAlways, ClientTemporalRefinement, ProtocolInvariant
<1>2. DerivedPointLogs /\ LiftedSafety!Inv => ReadIsolation /\ PartitionCommandsIndependent
    BY PointLift!CanonicalPointLogsImplyReplicaPointLogs, PointLiftParameters,
       PointLiftStateIdentities, PointLiftInterfaceIdentities
       DEF DerivedPointLogs, LiftedSafety!Inv, LiftedSafety!ProofInvariant,
           LiftedSafety!PreProvenanceInvariant, LiftedSafety!RecoveryInvariant,
           PointLift!ParameterAssumptions, PointLift!SentinelSeparation,
           PointLift!ClientParameters
<1> QED BY PTL, <1>1, <1>2
=============================================================================
