---------------------- MODULE TRaftCanonicalContextProof ---------------------
EXTENDS TRaftCanonicalUpdateProof, TRaftRecoveredContextProof, TRaftLogContextProof

THEOREM NormalCreationKeepsCanonicalContexts ==
    ASSUME ProofInvariant, GhostNext, Observe,
           NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE CanonicalContexts(canonical', entryContexts')
<1>1. formal[c] = canonical[term[c]] /\ formal[c] \subseteq Entries /\ IsFiniteSet(formal[c])
      /\ ContextSound(formal[c]) /\ CanonicalContexts(canonical, entryContexts)
      /\ term[c] \in Terms /\ formal \in [Replicas -> SUBSET Entries]
    BY SMT DEF CreateEntry, CreateSuccessor, ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData,
       CanonicalContexts, LogContexts, ContextSound
<1>2. formal'[c] = formal[c] \cup {NormalCreatedEntry(c, v, k, successor)}
      /\ role'[c] = "Leader" /\ term'[c] = term[c]
      /\ NormalCreatedEntry(c, v, k, successor).term = term[c]
    BY SMT, <1>1 DEF CreateEntry, CreateSuccessor, NormalCreatedEntry, Entry
<1>3. Cur(formal[c]) \in Int /\ \A x \in formal[c] : x.part \in Int /\ x.part <= Cur(formal[c])
    BY FiniteLogPartitionFrontier, <1>1
<1>4. NormalCreatedEntry(c, v, k, successor).part \in Int
      /\ \A x \in formal[c] : x.part \in Int /\ x.part <= NormalCreatedEntry(c, v, k, successor).part
    BY ONLY SMT, <1>3 DEF NormalCreatedEntry, Entry
<1>5. Prefix(formal'[c], NormalCreatedEntry(c, v, k, successor).part - 1)
        = Prefix(formal[c], NormalCreatedEntry(c, v, k, successor).part - 1)
    BY ONLY SMT, <1>2, <1>4 DEF Prefix
<1>50. Observe /\ c \in Replicas /\ NormalCreatedEntry(c, v, k, successor) \in formal'[c]
       /\ role'[c] = "Leader" /\ NormalCreatedEntry(c, v, k, successor).term = term'[c]
    BY SMT, <1>2
<1>51. entryContexts \subseteq entryContexts'
       /\ [entry |-> NormalCreatedEntry(c, v, k, successor),
           prefix |-> Prefix(formal'[c], NormalCreatedEntry(c, v, k, successor).part - 1)] \in entryContexts'
    BY ONLY ObservationIncludesLeaderContext, <1>50
<1>6. entryContexts \subseteq entryContexts'
      /\ [entry |-> NormalCreatedEntry(c, v, k, successor),
          prefix |-> Prefix(formal[c], NormalCreatedEntry(c, v, k, successor).part - 1)] \in entryContexts'
    BY ONLY ZenonT(5), <1>5, <1>51
<1>60. LogContexts(formal[c], entryContexts)
    BY <1>1 DEF ContextSound, LogContexts
<1>7. LogContexts(formal[c] \cup {NormalCreatedEntry(c, v, k, successor)}, entryContexts')
    BY ONLY AppendContextFromObservation, <1>4, <1>6, <1>60
<1>8. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
    BY NormalAppendCanonicalUpdate
<1> QED BY SMT, ContextsSurviveSourceGrowth, <1>1, <1>6, <1>7, <1>8 DEF CanonicalContexts

THEOREM RecoveryInputHasContexts ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipRecoveryUnion,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE ContextSound(Recovered(c, selected))
<1>1. CASE ReportedProposals(c) = {}
    <2>1. Recovered(c, selected) = {}
        BY EmptyReportRecoveryHasNoInput, <1>1
    <2> QED BY ONLY SMT, <2>1 DEF ContextSound
<1>2. CASE ReportedProposals(c) # {}
    <2>1. selected \in Latest(ReportedProposals(c))
        BY <1>2 DEF BuildRecovery
    <2> QED BY RecoveryMergePreservesContexts, <2>1
<1> QED BY <1>1, <1>2

THEOREM RecoveryKeepsCanonicalContexts ==
    ASSUME ProofInvariant, ElectionSafety, EntryContextUnique, ~MutSkipRecoveryUnion,
           GhostNext, Observe, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CanonicalContexts(canonical', entryContexts')
<1>1. Recovered(c, selected) \subseteq Entries /\ IsFiniteSet(Recovered(c, selected))
      /\ ContextSound(Recovered(c, selected))
    BY RecoveryInputIsFiniteTypedAndCoherent, RecoveryInputHasContexts
<1>2. Cur(Recovered(c, selected)) \in Int
      /\ \A x \in Recovered(c, selected) : x.part \in Int /\ x.part <= Cur(Recovered(c, selected))
    BY FiniteLogPartitionFrontier, <1>1
<1>3. RecoveryCreatedEntry(c, selected).part = Cur(Recovered(c, selected)) + 1
      /\ Prefix(Recovered(c, selected), RecoveryCreatedEntry(c, selected).part - 1) = Recovered(c, selected)
    BY ONLY SMT, <1>2 DEF RecoveryCreatedEntry, Entry, Prefix
<1>4. CreatedRecoveryProposal(c, selected) \in proposals'
    BY DEF BuildRecovery, CreatedRecoveryProposal, RecoveryCreatedEntry
<1>5. entryContexts \subseteq entryContexts'
      /\ [entry |-> RecoveryCreatedEntry(c, selected), prefix |-> Recovered(c, selected)] \in entryContexts'
    BY SMT, ObservationIncludesProposalContext, <1>4 DEF CreatedRecoveryProposal, Proposal
<1>50. LogContexts(Recovered(c, selected), entryContexts)
      /\ RecoveryCreatedEntry(c, selected).part \in Int
      /\ \A x \in Recovered(c, selected) : x.part \in Int /\ x.part <= RecoveryCreatedEntry(c, selected).part
    BY ONLY SMT, <1>1, <1>2, <1>3 DEF ContextSound, LogContexts
<1>6. LogContexts(Result(CreatedRecoveryProposal(c, selected)), entryContexts')
    BY ONLY AppendContextFromObservation, <1>3, <1>5, <1>50
       DEF CreatedRecoveryProposal, Proposal, Result
<1>7. CanonicalContexts(canonical, entryContexts) /\ term[c] \in Terms
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       CanonicalShape, ContextSound, CanonicalContexts, LogContexts
<1>8. canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1> QED BY SMT, ContextsSurviveSourceGrowth, <1>5, <1>6, <1>7, <1>8 DEF CanonicalContexts

THEOREM CanonicalContextsInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, EntryContextUnique, ~MutSkipRecoveryUnion,
           ProofNext, term' \in [Replicas -> Terms]
    PROVE CanonicalContexts(canonical', entryContexts')
<1>1. ProtocolNext /\ GhostNext /\ Observe
    BY DEF ProofNext, Next
<1>2. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryKeepsCanonicalContexts, <1>1, <1>2
<1>3. CASE NormalCreation
    BY NormalCreationKeepsCanonicalContexts, <1>1, <1>3 DEF NormalCreation
<1>4. CASE ~NormalCreation /\ ~\E c \in Replicas : \E selected : BuildRecovery(c, selected)
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyNormalCreationExtendsLeaderCanonical, OnlyRecoveryCreatesProposal, <1>1, <1>4
    <2>2. UNCHANGED canonical /\ entryContexts \subseteq entryContexts'
        BY NoNewSourceKeepsCanonical, <1>1, <2>1 DEF Observe
    <2>3. CanonicalContexts(canonical, entryContexts)
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape,
           ContextSound, CanonicalContexts, LogContexts
    <2> QED BY SMT, ContextsSurviveSourceGrowth, <2>2, <2>3 DEF CanonicalContexts
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
