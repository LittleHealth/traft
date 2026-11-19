---------------------- MODULE TRaftClientPartitionActions --------------------
EXTENDS TRaftNormalCreationInstances, TRaftPointPartitionProof

THEOREM SuccessorCreationPreservesPointLog ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW v, NEW k,
           CreateSuccessor(c, v, k), PointLog(formal[c]),
           k = "data" => v \in ClientCommands
    PROVE PointLog(formal[c] \cup {NormalCreatedEntry(c, v, k, TRUE)})
<1>1. formal[c] \subseteq Entries /\ IsFiniteSet(formal[c])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       FiniteLogInvariant, FiniteNodeData
<1>2. Cur(formal[c]) \in Int
      /\ \A x \in formal[c] : x.part \in Int /\ x.part <= Cur(formal[c])
    BY FiniteLogPartitionFrontier, <1>1
<1>3. \A x \in formal[c] : x.part # NormalCreatedEntry(c, v, k, TRUE).part
    BY ONLY SMT, <1>2 DEF NormalCreatedEntry, Entry
<1>4. NormalCreatedEntry(c, v, k, TRUE).kind = "data" =>
          NormalCreatedEntry(c, v, k, TRUE).value \in ClientCommands
    BY SMT DEF NormalCreatedEntry, Entry
<1> QED BY FreshPartitionPreservesPointLog, <1>3, <1>4

THEOREM AdmissionPreservesPointLog ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW q \in ClientCommands,
           Admit(c, q), PointLog(formal[c])
    PROVE PointLog(formal'[c])
<1>0. formal \in [Replicas -> SUBSET Entries]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>1. CASE MustSeparate(formal[c], q)
    <2>1. CreateSuccessor(c, q, "data")
          /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, q, "data", TRUE)}
        BY SMT, <1>0, <1>1 DEF Admit, CreateSuccessor, NormalCreatedEntry
    <2> QED BY SuccessorCreationPreservesPointLog, <2>1
<1>2. CASE ~MustSeparate(formal[c], q)
    <2>1. CreateEntry(c, q)
          /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, q, "data", FALSE)}
        BY SMT, <1>0, <1>2 DEF Admit, CreateEntry, NormalCreatedEntry
    <2>2. IsFiniteSet(formal[c])
        BY DEF ProofInvariant, PreProvenanceInvariant, FiniteLogInvariant, FiniteNodeData
    <2>3. q.op # "Get" /\ \A x \in formal[c] : x.part = Cur(formal[c]) /\ x.kind = "data" =>
              x.value.op # "Get" /\ x.value.key # q.key
        BY OpenPartitionAdmissionIsIndependent, <1>2, <2>2
    <2>4. PointLog(formal[c] \cup {NormalCreatedEntry(c, q, "data", FALSE)})
        BY IndependentAppendPreservesPointLog, <2>3 DEF NormalCreatedEntry, Entry
    <2> QED BY <2>1, <2>4
<1> QED BY <1>1, <1>2

THEOREM ClientCreationPreservesCanonicalPointLogs ==
    ASSUME ProofInvariant, GhostNext, CanonicalPointLogs(canonical),
           NEW c \in Replicas, NEW q \in ClientCommands, Admit(c, q)
    PROVE CanonicalPointLogs(canonical')
<1>0. CanonicalPointLogs(canonical)
    OBVIOUS
<1>01. role[c] = "Leader"
    BY DEF Admit, CreateEntry, CreateSuccessor
<1>02. formal \in [Replicas -> SUBSET Entries] /\ term \in [Replicas -> Terms]
       /\ \A r \in Replicas : role[r] = "Leader" => formal[r] = canonical[term[r]]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>1. formal[c] = canonical[term[c]] /\ term[c] \in Terms
    BY SMT, <1>01, <1>02
<1>2. PointLog(formal[c]) /\ PointLog(formal'[c])
    BY SMT, AdmissionPreservesPointLog, <1>1 DEF CanonicalPointLogs
<1>3. CASE MustSeparate(formal[c], q)
    <2>1. CreateSuccessor(c, q, "data")
          /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, q, "data", TRUE)}
        BY SMT, <1>02, <1>3 DEF Admit, CreateSuccessor, NormalCreatedEntry
    <2>2. canonical' = [t \in Terms |-> IF t = term[c]
              THEN canonical[t] \cup {NormalCreatedEntry(c, q, "data", TRUE)} ELSE canonical[t]]
        BY SuccessorCanonicalUpdate, <2>1
    <2> QED BY ONLY ZenonT(5), <1>0, <1>1, <1>2, <2>1, <2>2 DEF CanonicalPointLogs
<1>4. CASE ~MustSeparate(formal[c], q)
    <2>1. CreateEntry(c, q)
          /\ formal'[c] = formal[c] \cup {NormalCreatedEntry(c, q, "data", FALSE)}
        BY SMT, <1>02, <1>4 DEF Admit, CreateEntry, NormalCreatedEntry
    <2>2. canonical' = [t \in Terms |-> IF t = term[c]
              THEN canonical[t] \cup {NormalCreatedEntry(c, q, "data", FALSE)} ELSE canonical[t]]
        BY OpenEntryCanonicalUpdate, <2>1
    <2> QED BY ONLY ZenonT(5), <1>0, <1>1, <1>2, <2>1, <2>2 DEF CanonicalPointLogs
<1> QED BY <1>3, <1>4

THEOREM ClosingPreservesCanonicalPointLogs ==
    ASSUME ProofInvariant, GhostNext, CanonicalPointLogs(canonical),
           NEW c \in Replicas, ClosePartition(c)
    PROVE CanonicalPointLogs(canonical')
<1>1. CreateSuccessor(c, NoValue, "noop")
      /\ formal[c] = canonical[term[c]] /\ term[c] \in Terms
    <2>1. CreateSuccessor(c, NoValue, "noop")
        BY DEF ClosePartition
    <2>2. role[c] = "Leader"
        BY <2>1 DEF CreateSuccessor
    <2>3. term \in [Replicas -> Terms]
          /\ \A r \in Replicas : role[r] = "Leader" => formal[r] = canonical[term[r]]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3
<1>2. PointLog(formal[c] \cup {NormalCreatedEntry(c, NoValue, "noop", TRUE)})
    BY SuccessorCreationPreservesPointLog, <1>1 DEF CanonicalPointLogs
<1>3. canonical' = [t \in Terms |-> IF t = term[c]
           THEN canonical[t] \cup {NormalCreatedEntry(c, NoValue, "noop", TRUE)} ELSE canonical[t]]
    BY SuccessorCanonicalUpdate, <1>1
<1> QED BY ZenonT(5), <1>1, <1>2, <1>3 DEF CanonicalPointLogs

THEOREM RecoveredPointLog ==
    ASSUME ProofInvariant, CanonicalPointLogs(canonical),
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE PointLog(Recovered(c, selected))
<1>1. CASE ReportedProposals(c) = {}
    BY EmptyPointLog, EmptyReportRecoveryHasNoInput, <1>1
<1>2. CASE ReportedProposals(c) # {}
    <2>1. selected \in Latest(ReportedProposals(c)) /\ selected \in proposals /\ selected.epoch \in Terms
        BY SelectedRecoveryProposalIsActual, <1>2
    <2>2. Recovered(c, selected) \subseteq canonical[selected.epoch]
        BY RecoveredIsCanonicalSubset, <2>1
    <2> QED BY PointLogInheritedBySubset, <2>1, <2>2 DEF CanonicalPointLogs
<1> QED BY <1>1, <1>2

THEOREM RecoveryPreservesCanonicalPointLogs ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext, CanonicalPointLogs(canonical),
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CanonicalPointLogs(canonical')
<1>1. PointLog(Recovered(c, selected))
      /\ IsFiniteSet(Recovered(c, selected)) /\ Recovered(c, selected) \subseteq Entries
    BY RecoveredPointLog, RecoveryInputIsFiniteTypedAndCoherent
<1>2. Cur(Recovered(c, selected)) \in Int
      /\ \A x \in Recovered(c, selected) : x.part \in Int /\ x.part <= Cur(Recovered(c, selected))
    BY FiniteLogPartitionFrontier, <1>1
<1>3. \A x \in Recovered(c, selected) : x.part # RecoveryCreatedEntry(c, selected).part
    BY ONLY SMT, <1>2 DEF RecoveryCreatedEntry, Entry
<1>4. PointLog(Result(CreatedRecoveryProposal(c, selected)))
    BY FreshPartitionPreservesPointLog, <1>1, <1>3
       DEF CreatedRecoveryProposal, RecoveryCreatedEntry, Entry, Proposal, Result
<1>5. canonical' = [t \in Terms |-> IF t = term[c]
           THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1> QED BY ZenonT(5), <1>4, <1>5 DEF CanonicalPointLogs
=============================================================================
