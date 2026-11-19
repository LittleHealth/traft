----------------------- MODULE TRaftApplicationAgreement ---------------------
EXTENDS TRaftApplicationInterpretation, TRaftApplicationPrefixTemporal,
        TRaftClientApplicationTemporal, TRaftReadResultAgreement

SameAppliedSetAgreement == \A r, s \in Replicas : applied[r] = applied[s] =>
    machine[r] = machine[s] /\ cache[r] = cache[s]

THEOREM ReadLiftParameters ==
    /\ PointLift!ClientParameters
    /\ PointLift!ParameterAssumptions
    /\ PointLift!SentinelSeparation
BY ONLY PointLiftParameters

THEOREM ReadLiftStateIdentity ==
    PointLift!ProofInvariant <=> LiftedSafety!ProofInvariant
BY ONLY PointLiftStateIdentities

THEOREM ReadLiftInterfaceIdentities ==
    /\ PointLift!CommitEvidenceSound = CommitEvidenceSound
    /\ PointLift!EntryContextUnique = EntryContextUnique
    /\ PointLift!AppliedEntriesPreserved = AppliedEntriesPreserved
    /\ PointLift!AppliedPrefixClosure = AppliedPrefixClosure
    /\ PointLift!RequestIdentityState = RequestIdentityState
    /\ PointLift!ApplicationMatchesAppliedSet = ApplicationMatchesAppliedSet
    /\ PointLift!ReadyResultsAgree = ReadyResultsAgree
BY ONLY
   DEF PointLift!ApplicationMatchesAppliedSet, ApplicationMatchesAppliedSet, PointLift!AppliedCache,
       AppliedCache, PointLift!AppliedEntriesPreserved, AppliedEntriesPreserved,
       PointLift!AppliedMachine, AppliedMachine, PointLift!AppliedPrefixClosure,
       AppliedPrefixClosure, PointLift!ClientCommands, ClientCommands,
       PointLift!CommitEvidenceSound, CommitEvidenceSound, PointLift!Cur, Cur,
       PointLift!EntryContextUnique, EntryContextUnique, PointLift!Evidence, Evidence,
       PointLift!FirstRequestEntries, FirstRequestEntries, PointLift!Keys, Keys,
       PointLift!LastWriteValue, LastWriteValue, PointLift!MaxOr, MaxOr, PointLift!MessageAckers,
       MessageAckers, PointLift!PointWrites, PointWrites, PointLift!PointWritesBefore,
       PointWritesBefore, PointLift!Prefix, Prefix, PointLift!PrefixClosed, PrefixClosed,
       PointLift!Quorum, Quorum, PointLift!ReadyResultsAgree, ReadyResultsAgree,
       PointLift!RequestEntries, RequestEntries, PointLift!RequestIdentityState,
       RequestIdentityState, PointLift!RequestIds, RequestIds, PointLift!SeqDomain, SeqDomain,
       PointLift!Terms, Terms, PointLift!WriteValue, WriteValue, PointLift!IsFiniteSet, IsFiniteSet,
       PointLift!Cardinality, Cardinality, PointLift!Seq, Seq, PointLift!Len, Len, PointLift!Append,
       Append

THEOREM LiftedFiniteLogIdentity == LiftedSafety!FiniteLogInvariant <=> FiniteLogInvariant
BY ONLY
   DEF LiftedSafety!FiniteChannels, FiniteChannels, LiftedSafety!FiniteLogInvariant,
       FiniteLogInvariant, LiftedSafety!FiniteNodeData, FiniteNodeData,
       LiftedSafety!FiniteProposals, FiniteProposals, LiftedSafety!FiniteSnapshots,
       FiniteSnapshots, LiftedSafety!Result, Result, LiftedSafety!StorageShape, StorageShape,
       LiftedSafety!IsFiniteSet, IsFiniteSet, LiftedSafety!Cardinality, Cardinality

THEOREM ClientPointGoalsDescribePointLogs ==
    (ClientApplicationSources /\ ReadIsolation /\ PartitionCommandsIndependent)
        => \A r \in Replicas : PointLog(formal[r])
BY DEF ClientApplicationSources, ReadIsolation, PartitionCommandsIndependent, PointLog

THEOREM ClientApplicationLogFactsAlways ==
    ASSUME NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []ApplicationLogFacts
<1>1. ClientSpecification(Extra) =>
          []LiftedSafety!Inv /\ []RequestIdentityState /\ []DerivedRequestSources
          /\ []AppliedPrefixClosure /\ [](ReadIsolation /\ PartitionCommandsIndependent)
    BY PTL, ClientTemporalRefinement, ProtocolInvariant, ClientRequestIdentityAlways,
       ClientRequestSourcesAlways, ApplicationPrefixesAlwaysClosed, ClientPartitionIndependence
<1>2. DerivedRequestSources /\ LiftedSafety!Inv /\ RequestIdentityState
      /\ AppliedPrefixClosure /\ ReadIsolation /\ PartitionCommandsIndependent => ApplicationLogFacts
    BY DerivedSourcesReachApplication, ClientPointGoalsDescribePointLogs,
       LiftedSafetyPredicateIdentity, LiftedFiniteLogIdentity
       DEF ApplicationLogFacts, LiftedSafety!Inv, Safety, LiftedSafety!ProofInvariant,
           LiftedSafety!PreProvenanceInvariant, FormalDataFrom, LogDataFrom
<1> QED BY PTL, <1>1, <1>2

THEOREM ClientApplicationInterpretationAlways ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []ApplicationMatchesAppliedSet
<1>1. ClientSpecification(Extra) =>
          []ApplicationLogFacts /\ [](ApplicationTypes /\ ReadyIdsMatchApplied)
    BY PTL, ClientApplicationLogFactsAlways, ClientApplicationFactsAlways
<1>2. ClientInit => ApplicationMatchesAppliedSet
    BY ApplicationInterpretationInitially
<1>3. ApplicationMatchesAppliedSet /\ ApplicationLogFacts /\ ApplicationTypes /\ ReadyIdsMatchApplied
      /\ [ClientAction /\ Observe /\ Extra]_clientVars => ApplicationMatchesAppliedSet'
    BY SMT, ApplicationInterpretationInductiveStep
       DEF ApplicationMatchesAppliedSet, clientVars, vars, protocolVars, localClientVars
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification

\* Equal applied sets include the same first occurrence of each request.
\* This target concerns equal applied sets. The separate ApplicationAgreement
\* theorem below also derives ready-result agreement across different progress.
THEOREM ClientSameAppliedSetAgreement ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []SameAppliedSetAgreement
<1>1. ApplicationMatchesAppliedSet => SameAppliedSetAgreement
    BY EqualAppliedSetsDetermineEqualApplication DEF SameAppliedSetAgreement
<1> QED BY PTL, ClientApplicationInterpretationAlways, <1>1

THEOREM ApplicationAgreement ==
    ASSUME ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => [](SameAppliedSetAgreement /\ ReadyResultsAgree)
<1>1. ClientSpecification(Extra) =>
          []SameAppliedSetAgreement /\ []ApplicationMatchesAppliedSet
          /\ []ApplicationLogFacts /\ []LiftedSafety!Inv
    BY PTL, ClientSameAppliedSetAgreement, ClientApplicationInterpretationAlways,
       ClientApplicationLogFactsAlways, ClientTemporalRefinement, ProtocolInvariant
<1>2. ApplicationMatchesAppliedSet /\ ApplicationLogFacts /\ LiftedSafety!Inv => ReadyResultsAgree
    BY PointLift!CandidateReadyResultsAgree, ReadLiftParameters, ReadLiftStateIdentity,
       ReadLiftInterfaceIdentities, LiftedSafetyPredicateIdentity
       DEF ApplicationLogFacts, LiftedSafety!Inv, Safety, PointLift!ClientParameters, PointLift!ParameterAssumptions, PointLift!SentinelSeparation
<1> QED BY PTL, <1>1, <1>2
=============================================================================
