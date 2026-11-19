--------------------- MODULE TRaftClientPartitionInduction -------------------
EXTENDS TRaftClientPartitionActions, TRaftClientPersistenceProof

THEOREM OnlyAdmissionExtendsLeaderPointLog ==
    ASSUME ProofInvariant, ElectionSafety, ClientAction
    PROVE (\E c \in Replicas : \E q \in calls : Admit(c, q))
       \/ (\E c \in Replicas : ClosePartition(c)) \/ PostLeaderBound
<1>0. LeaderData
    BY CandidateHasLeaderData
<1>00. ClientAction
    OBVIOUS
<1>1. Background => PostLeaderBound
    BY AdministrativeActionsKeepLeaderCanonicalBound DEF Background
<1>2. \A q : Invoke(q) => PostLeaderBound
    BY SMT, <1>0 DEF Invoke, protocolVars, LeaderData, PostLeaderBound
<1>3. \A r \in Replicas : \A e : ApplyClient(r, e) => PostLeaderBound
    BY SMT, <1>0 DEF ApplyClient, ApplyEntry, LeaderData, PostLeaderBound
<1>4. \A r, q : (SendReply(r, q) \/ ReadWithoutBarrier(r, q)) => PostLeaderBound
    BY SMT, <1>0 DEF SendReply, ReadWithoutBarrier, protocolVars, LeaderData, PostLeaderBound
<1>5. \A m : ReceiveReply(m) => PostLeaderBound
    BY SMT, <1>0 DEF ReceiveReply, protocolVars, LeaderData, PostLeaderBound
<1> QED BY ONLY SMT, <1>00, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ClientAction

THEOREM OnlyClientRecoveryCreatesProposal == ClientAction =>
    (\E c \in Replicas : \E selected : BuildRecovery(c, selected)) \/ UNCHANGED proposals
<1>1. Background =>
          (\E c \in Replicas : \E selected : BuildRecovery(c, selected)) \/ UNCHANGED proposals
    BY OnlyRecoveryCreatesProposal DEF Background, ProtocolNext
<1>2. \A q : Invoke(q) => UNCHANGED proposals
    BY SMT DEF Invoke, protocolVars
<1>3. \A c, q : Admit(c, q) => UNCHANGED proposals
    BY SMT DEF Admit, CreateEntry, CreateSuccessor
<1>4. \A c : ClosePartition(c) => UNCHANGED proposals
    BY SMT DEF ClosePartition, CreateSuccessor
<1>5. \A r, e : ApplyClient(r, e) => UNCHANGED proposals
    BY SMT DEF ApplyClient, ApplyEntry
<1>6. \A r, q : (SendReply(r, q) \/ ReadWithoutBarrier(r, q)) => UNCHANGED proposals
    BY SMT DEF SendReply, ReadWithoutBarrier, protocolVars
<1>7. \A m : ReceiveReply(m) => UNCHANGED proposals
    BY SMT DEF ReceiveReply, protocolVars
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ClientAction

THEOREM ClientPointLogInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, RequestIdentityState, ClientAction, GhostNext,
           term' \in [Replicas -> Terms], CanonicalPointLogs(canonical)
    PROVE CanonicalPointLogs(canonical')
<1>1. CASE \E c \in Replicas : \E q \in calls : Admit(c, q)
    BY ClientCreationPreservesCanonicalPointLogs, <1>1 DEF RequestIdentityState
<1>2. CASE \E c \in Replicas : ClosePartition(c)
    BY ClosingPreservesCanonicalPointLogs, <1>2
<1>3. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryPreservesCanonicalPointLogs, <1>3
<1>4. CASE ~(\E c \in Replicas : \E q \in calls : Admit(c, q))
          /\ ~(\E c \in Replicas : ClosePartition(c))
          /\ ~(\E c \in Replicas : \E selected : BuildRecovery(c, selected))
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyAdmissionExtendsLeaderPointLog, OnlyClientRecoveryCreatesProposal, <1>4
    <2>2. UNCHANGED canonical
        BY NoNewSourceKeepsCanonical, <2>1
    <2> QED BY <2>2
<1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM CanonicalPointLogsImplyReplicaPointLogs ==
    ASSUME CanonicalShape, CanonicalPointLogs(canonical)
    PROVE ReadIsolation /\ PartitionCommandsIndependent
<1>1. ASSUME NEW r \in Replicas
      PROVE PointLog(formal[r])
    <2>1. CASE formal[r] = {}
        BY EmptyPointLog, <2>1
    <2>2. CASE formal[r] # {}
        <3>1. LastTerm(formal[r]) \in Terms /\ formal[r] \subseteq canonical[LastTerm(formal[r])]
            BY <1>1, <2>2 DEF CanonicalShape, Sublog
        <3> QED BY PointLogInheritedBySubset, <3>1 DEF CanonicalPointLogs
    <2> QED BY <2>1, <2>2
<1> QED BY PointPropertiesImplyClientPartitionGoals, <1>1
=============================================================================
