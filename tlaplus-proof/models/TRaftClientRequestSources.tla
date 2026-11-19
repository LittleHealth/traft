----------------------- MODULE TRaftClientRequestSources ---------------------
EXTENDS TRaftClientPartitionInduction

LogDataFrom(L, Q) == \A e \in L : e.kind = "data" => e.value \in Q
CanonicalDataFrom(C, Q) == \A t \in Terms : LogDataFrom(C[t], Q)
FormalDataFrom(F, Q) == \A r \in Replicas : LogDataFrom(F[r], Q)

THEOREM ClientCallsNeverShrink == ClientAction => calls \subseteq calls'
<1>1. ClientAction => (\E q \in ClientCommands : Invoke(q)) \/ UNCHANGED calls
    BY OnlyInvocationChangesRequestIdentity
<1>2. \A q : Invoke(q) => calls \subseteq calls'
    BY DEF Invoke
<1> QED BY SMT, <1>1, <1>2

THEOREM DataSourceRestrictionAndGrowth ==
    ASSUME NEW L, NEW M, NEW Q, NEW R, LogDataFrom(L, Q), M \subseteq L, Q \subseteq R
    PROVE LogDataFrom(M, R)
BY SMT DEF LogDataFrom

THEOREM SuccessorKeepsRequestSources ==
    ASSUME ProofInvariant, GhostNext, CanonicalDataFrom(canonical, calls), calls \subseteq calls',
           NEW c \in Replicas, NEW v, NEW k, k = "data" => v \in calls,
           CreateSuccessor(c, v, k)
    PROVE CanonicalDataFrom(canonical', calls')
<1>1. NormalCreatedEntry(c, v, k, TRUE).kind = k
      /\ NormalCreatedEntry(c, v, k, TRUE).value = v
    BY SMT DEF NormalCreatedEntry, Entry
<1>2. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, TRUE)} ELSE canonical[t]]
    BY SuccessorCanonicalUpdate
<1> QED BY ZenonT(5), <1>1, <1>2 DEF CanonicalDataFrom, LogDataFrom

THEOREM OpenEntryKeepsRequestSources ==
    ASSUME ProofInvariant, GhostNext, CanonicalDataFrom(canonical, calls), calls \subseteq calls',
           NEW c \in Replicas, NEW v \in calls, CreateEntry(c, v)
    PROVE CanonicalDataFrom(canonical', calls')
<1>1. NormalCreatedEntry(c, v, "data", FALSE).kind = "data"
      /\ NormalCreatedEntry(c, v, "data", FALSE).value = v
    BY SMT DEF NormalCreatedEntry, Entry
<1>2. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, "data", FALSE)} ELSE canonical[t]]
    BY OpenEntryCanonicalUpdate
<1> QED BY ZenonT(5), <1>1, <1>2 DEF CanonicalDataFrom, LogDataFrom

THEOREM RecoveryInputKeepsRequestSources ==
    ASSUME ProofInvariant, CanonicalDataFrom(canonical, calls),
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE LogDataFrom(Recovered(c, selected), calls)
<1>1. CASE ReportedProposals(c) = {}
    <2>1. Recovered(c, selected) = {}
        BY EmptyReportRecoveryHasNoInput, <1>1
    <2> QED BY ONLY <2>1 DEF LogDataFrom
<1>2. CASE ReportedProposals(c) # {}
    <2>1. selected \in Latest(ReportedProposals(c)) /\ selected \in proposals /\ selected.epoch \in Terms
        BY SelectedRecoveryProposalIsActual, <1>2
    <2>2. Recovered(c, selected) \subseteq canonical[selected.epoch]
        BY RecoveredIsCanonicalSubset, <2>1
    <2> QED BY DataSourceRestrictionAndGrowth, <2>1, <2>2 DEF CanonicalDataFrom
<1> QED BY <1>1, <1>2

THEOREM RecoveryKeepsRequestSources ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext, CanonicalDataFrom(canonical, calls),
           calls \subseteq calls', NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CanonicalDataFrom(canonical', calls')
<1>1. LogDataFrom(Recovered(c, selected), calls)
    BY RecoveryInputKeepsRequestSources
<1>2. LogDataFrom(Result(CreatedRecoveryProposal(c, selected)), calls')
    BY SMT, <1>1 DEF LogDataFrom, CreatedRecoveryProposal, RecoveryCreatedEntry, Entry, Proposal, Result
<1>3. canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1> QED BY SMT, DataSourceRestrictionAndGrowth, <1>2, <1>3 DEF CanonicalDataFrom

THEOREM ClientRequestSourcesInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ClientAction, GhostNext,
           term' \in [Replicas -> Terms], CanonicalDataFrom(canonical, calls)
    PROVE CanonicalDataFrom(canonical', calls')
<1>0. calls \subseteq calls'
    BY ClientCallsNeverShrink
<1>1. CASE \E c \in Replicas : \E q \in calls : Admit(c, q)
    <2>1. PICK c \in Replicas, q \in calls : Admit(c, q)
        BY <1>1
    <2>2. CreateEntry(c, q) \/ CreateSuccessor(c, q, "data")
        BY <2>1 DEF Admit
    <2> QED BY SuccessorKeepsRequestSources, OpenEntryKeepsRequestSources, <1>0, <2>1, <2>2
<1>2. CASE \E c \in Replicas : ClosePartition(c)
    BY SuccessorKeepsRequestSources, <1>0, <1>2 DEF ClosePartition
<1>3. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryKeepsRequestSources, <1>0, <1>3
<1>4. CASE ~(\E c \in Replicas : \E q \in calls : Admit(c, q))
          /\ ~(\E c \in Replicas : ClosePartition(c))
          /\ ~(\E c \in Replicas : \E selected : BuildRecovery(c, selected))
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyAdmissionExtendsLeaderPointLog, OnlyClientRecoveryCreatesProposal, <1>4
    <2>2. UNCHANGED canonical
        BY NoNewSourceKeepsCanonical, <2>1
    <2> QED BY SMT, DataSourceRestrictionAndGrowth, <1>0, <2>2 DEF CanonicalDataFrom
<1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM CanonicalRequestSourcesReachReplicas ==
    ASSUME CanonicalShape, CanonicalDataFrom(canonical, calls)
    PROVE FormalDataFrom(formal, calls)
<1>1. ASSUME NEW r \in Replicas
      PROVE LogDataFrom(formal[r], calls)
    <2>1. CASE formal[r] = {}
        BY <2>1 DEF LogDataFrom
    <2>2. CASE formal[r] # {}
        <3>1. LastTerm(formal[r]) \in Terms /\ formal[r] \subseteq canonical[LastTerm(formal[r])]
            BY <1>1, <2>2 DEF CanonicalShape, Sublog
        <3> QED BY DataSourceRestrictionAndGrowth, <3>1 DEF CanonicalDataFrom
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1 DEF FormalDataFrom
=============================================================================
