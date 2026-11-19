---------------------- MODULE TRaftClientTraceInterface ----------------------
EXTENDS TRaftApplicationAgreement, TRaftClientHistoryTemporal,
        TRaftClientReturnedWitness, TRaftEvidenceLinearizationOrder

\* Proof decomposition only. Every imported theorem is checked separately.
\* No executable action, observer, state predicate or target is strengthened.

THEOREM TraceLiftParameters ==
    /\ PointLift!ClientParameters
    /\ PointLift!ParameterAssumptions
    /\ PointLift!SentinelSeparation
BY ONLY PointLiftParameters

THEOREM TraceLiftStateIdentity ==
    PointLift!ProofInvariant <=> LiftedSafety!ProofInvariant
BY ONLY PointLiftStateIdentities

THEOREM TraceLiftInterfaceIdentities ==
    /\ PointLift!CommitEvidenceSound = CommitEvidenceSound
    /\ PointLift!EntryContextUnique = EntryContextUnique
    /\ PointLift!AppliedEntriesPreserved = AppliedEntriesPreserved
    /\ PointLift!AppliedPrefixClosure = AppliedPrefixClosure
    /\ PointLift!ApplicationMatchesAppliedSet = ApplicationMatchesAppliedSet
    /\ PointLift!RequestIdentityState = RequestIdentityState
    /\ PointLift!WitnessRepresentation = WitnessRepresentation
    /\ PointLift!ReplySources = ReplySources
    /\ PointLift!ReturnedMessagesHaveSource = ReturnedMessagesHaveSource
    /\ PointLift!ReturnedWitnessAgreement = ReturnedWitnessAgreement
    /\ PointLift!EvidenceEntries = EvidenceEntries
    /\ PointLift!Entries = Entries
    /\ PointLift!Terms = Terms
    /\ \A aliasArg1 : PointLift!PointLog(aliasArg1) = PointLog(aliasArg1)
    /\ \A aliasArg1 : PointLift!Coherent(aliasArg1) = Coherent(aliasArg1)
    /\ \A aliasArg1 : PointLift!IsFiniteSet(aliasArg1) = IsFiniteSet(aliasArg1)
BY ONLY
   DEF PointLift!ApplicationMatchesAppliedSet, ApplicationMatchesAppliedSet,
       PointLift!AppliedCache, AppliedCache, PointLift!AppliedEntriesPreserved,
       AppliedEntriesPreserved, PointLift!AppliedMachine, AppliedMachine,
       PointLift!AppliedPointState, AppliedPointState, PointLift!AppliedPrefixClosure,
       AppliedPrefixClosure, PointLift!ClientCommands, ClientCommands, PointLift!Coherent,
       Coherent, PointLift!Command, Command, PointLift!CommitEvidenceSound, CommitEvidenceSound,
       PointLift!Cur, Cur, PointLift!Effect, Effect, PointLift!EmptyAnswers, EmptyAnswers,
       PointLift!EmptyMachine, EmptyMachine, PointLift!Entries, Entries,
       PointLift!EntryContextUnique, EntryContextUnique, PointLift!EntryRequestIds,
       EntryRequestIds, PointLift!Evidence, Evidence, PointLift!EvidenceEntries, EvidenceEntries,
       PointLift!FirstRequestEntries, FirstRequestEntries, PointLift!Fold, Fold,
       PointLift!FoldExecuteOrder, FoldExecuteOrder, PointLift!FoldTrace, FoldTrace,
       PointLift!Ids, Ids, PointLift!Indices, Indices, PointLift!Keys, Keys,
       PointLift!LastWriteValue, LastWriteValue, PointLift!MaxOr, MaxOr, PointLift!MessageAckers,
       MessageAckers, PointLift!Part, Part, PointLift!Partitions, Partitions, PointLift!PointLog,
       PointLog, PointLift!PointWrites, PointWrites, PointLift!PointWritesBefore,
       PointWritesBefore, PointLift!Prefix, Prefix, PointLift!PrefixClosed, PrefixClosed,
       PointLift!Quorum, Quorum, PointLift!Reply, Reply, PointLift!ReplyHasDurableSource,
       ReplyHasDurableSource, PointLift!ReplySources, ReplySources, PointLift!RequestEntries,
       RequestEntries, PointLift!RequestIdentityState, RequestIdentityState, PointLift!RequestIds,
       RequestIds, PointLift!ReturnedIds, ReturnedIds, PointLift!ReturnedMessagesHaveSource,
       ReturnedMessagesHaveSource, PointLift!ReturnedWitnessAgreement, ReturnedWitnessAgreement,
       PointLift!SeqDomain, SeqDomain, PointLift!SequentialRequestStep, SequentialRequestStep,
       PointLift!Terms, Terms, PointLift!UniqueOrder, UniqueOrder, PointLift!WitnessCache,
       WitnessCache, PointLift!WitnessPoint, WitnessPoint, PointLift!WitnessRepresentation,
       WitnessRepresentation, PointLift!WitnessSequential, WitnessSequential,
       PointLift!WitnessStateNow, WitnessStateNow, PointLift!WitnessStates, WitnessStates,
       PointLift!WriteValue, WriteValue, PointLift!IsFiniteSet, IsFiniteSet,
       PointLift!Cardinality, Cardinality, PointLift!Seq, Seq, PointLift!Len, Len,
       PointLift!Append, Append

THEOREM OrderLiftParameters ==
    /\ PointLift!ParameterAssumptions
    /\ PointLift!SentinelSeparation
    /\ PointLift!FormalFaultsDisabled
    /\ PointLift!ClientParameters
BY ONLY PointLiftParameters

THEOREM OrderLiftStateIdentity ==
    PointLift!Inv <=> LiftedSafety!Inv
BY ONLY SMT, PointLiftStateIdentities, PointCoreAliasSafety, LiftedSafetyPredicateIdentity
   DEF PointLift!Inv, LiftedSafety!Inv

THEOREM OrderLiftInterfaceIdentities ==
    /\ PointLift!Next = Next
    /\ PointLift!NewEvidenceFollowsOldPartitions = NewEvidenceFollowsOldPartitions
BY ONLY SMT, PointCoreAliasNext
   DEF PointLift!NewEvidenceFollowsOldPartitions, NewEvidenceFollowsOldPartitions,
       PointLift!EvidenceEntries, EvidenceEntries
=============================================================================
