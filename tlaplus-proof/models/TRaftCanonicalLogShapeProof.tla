--------------------- MODULE TRaftCanonicalLogShapeProof ---------------------
EXTENDS TRaftCanonicalUpdateProof, TRaftLogCountProof

THEOREM CandidateHasCanonicalLogShape == ProofInvariant => CanonicalLogShape(canonical)
BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape,
       CanonicalLogShape, BoundedLogCounts

THEOREM NormalCreationKeepsCanonicalLogShape ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE CanonicalLogShape(canonical')
<1>0. CanonicalLogShape(canonical) /\ MaxPartitionSize \in Nat /\ MaxPartitionSize > 0
    BY CandidateHasCanonicalLogShape, ParameterAssumptions DEF ParameterAssumptions
<1>10. formal[c] = canonical[term[c]] /\ formal[c] \subseteq Entries /\ IsFiniteSet(formal[c])
      /\ term[c] \in Terms
    BY SMT DEF CreateEntry, CreateSuccessor, ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData
<1>1. formal[c] = canonical[term[c]] /\ formal[c] \subseteq Entries /\ IsFiniteSet(formal[c])
      /\ term[c] \in Terms /\ BoundedLogCounts(formal[c]) /\ CanonicalLogShape(canonical)
    BY ONLY SMT, <1>0, <1>10 DEF CanonicalLogShape
<1>2. NormalCreatedEntry(c, v, k, successor) \in Entries
      /\ Coherent(formal[c] \cup {NormalCreatedEntry(c, v, k, successor)})
    BY NormalCreationIsTypedAndCoherent
<1>3. LastIndex(formal[c]) \in Nat /\ Cur(formal[c]) \in Int
      /\ \A x \in formal[c] : x.index <= LastIndex(formal[c]) /\ x.index \in Nat
    BY FiniteLogNumericFrontier, <1>1
<1>4. NormalCreatedEntry(c, v, k, successor) \notin formal[c]
      /\ NormalCreatedEntry(c, v, k, successor).term = term[c]
      /\ NormalCreatedEntry(c, v, k, successor).part \in Partitions
    BY SMT, <1>2, <1>3 DEF NormalCreatedEntry, Entry, Entries
<1>5. Count(formal[c], NormalCreatedEntry(c, v, k, successor).part) < MaxPartitionSize
    <2>1. CASE successor
        <3>1. Count(formal[c], NormalCreatedEntry(c, v, k, successor).part) = 0
            BY NewPartitionIsEmpty, <1>1, <2>1 DEF NormalCreatedEntry, Entry
        <3> QED BY ONLY SMT, <1>0, <3>1
    <2>2. CASE ~successor
        BY SMT, <2>2 DEF CreateEntry, NormalCreatedEntry, Entry
    <2> QED BY <2>1, <2>2
<1>6. BoundedLogCounts(formal[c] \cup {NormalCreatedEntry(c, v, k, successor)})
    BY AppendKeepsCountBound, <1>1, <1>4, <1>5
<1>7. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
    BY NormalAppendCanonicalUpdate
<1>8. formal[c] \cup {NormalCreatedEntry(c, v, k, successor)} \subseteq Entries
      /\ \A e \in formal[c] \cup {NormalCreatedEntry(c, v, k, successor)} : e.term <= term[c]
    BY SMT, <1>1, <1>2, <1>4 DEF CanonicalLogShape, Entries, Terms, ParameterAssumptions
<1>9. canonical' = [t \in Terms |-> IF t = term[c]
                THEN formal[c] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
    BY ONLY SMT, <1>1, <1>7
<1> QED BY ONLY ReplaceCanonicalLogShape, <1>1, <1>2, <1>6, <1>8, <1>9

THEOREM RecoveryInputHasBoundedCounts ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE BoundedLogCounts(Recovered(c, selected))
<1>0. MaxPartitionSize \in Nat /\ MaxPartitionSize > 0
    BY ParameterAssumptions DEF ParameterAssumptions
<1>1. CASE ReportedProposals(c) = {}
    BY SMT, EmptyLogFrontier, <1>0, <1>1 DEF BuildRecovery, Recovered, BoundedLogCounts
<1>2. CASE ReportedProposals(c) # {}
    <2>10. selected \in Latest(ReportedProposals(c)) /\ selected \in ReportedProposals(c)
        BY <1>2 DEF BuildRecovery, Latest
    <2>11. ReportedProposals(c) \subseteq proposals
        BY ReportedProposalsAreActual
    <2>12. \A p \in proposals : p.epoch \in Terms
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>1. selected \in Latest(ReportedProposals(c)) /\ selected \in proposals /\ selected.epoch \in Terms
        BY ONLY <2>10, <2>11, <2>12
    <2>2. Recovered(c, selected) \subseteq canonical[selected.epoch]
        BY RecoveredIsCanonicalSubset, <2>1
    <2>3. \A p \in Partitions : Count(Recovered(c, selected), p) \in 0..MaxPartitionSize
        BY CanonicalSubsetHasBoundedCounts, <2>1, <2>2
    <2>4. MaxPartitionSize \in Nat
        BY <1>0
    <2> QED BY ONLY SMT, <2>3, <2>4 DEF BoundedLogCounts
<1> QED BY <1>1, <1>2

THEOREM RecoveryKeepsCanonicalLogShape ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CanonicalLogShape(canonical')
<1>0. MaxPartitionSize \in Nat /\ MaxPartitionSize > 0 /\ Terms \subseteq Nat
    BY ParameterAssumptions DEF ParameterAssumptions
<1>1. Recovered(c, selected) \subseteq Entries /\ IsFiniteSet(Recovered(c, selected))
      /\ BoundedLogCounts(Recovered(c, selected))
    BY RecoveryInputIsFiniteTypedAndCoherent, RecoveryInputHasBoundedCounts
<1>2. CreatedRecoveryProposal(c, selected) \in ProposalRecords
      /\ Coherent(Result(CreatedRecoveryProposal(c, selected)))
    BY RecoveryCreationIsTypedAndCoherent
<1>3. \A e \in Recovered(c, selected) : e.term < term[c]
    BY RecoveryOnlyCopiesOlderCreationTerms
<1>4. RecoveryCreatedEntry(c, selected) \in Entries
      /\ RecoveryCreatedEntry(c, selected).part = Cur(Recovered(c, selected)) + 1
      /\ RecoveryCreatedEntry(c, selected).term = term[c]
    <2>1. CreatedRecoveryProposal(c, selected).first \in Entries
        BY ONLY <1>2 DEF ProposalRecords
    <2>2. CreatedRecoveryProposal(c, selected).first = RecoveryCreatedEntry(c, selected)
        BY DEF CreatedRecoveryProposal, Proposal
    <2>3. RecoveryCreatedEntry(c, selected).part = Cur(Recovered(c, selected)) + 1
          /\ RecoveryCreatedEntry(c, selected).term = term[c]
        BY DEF RecoveryCreatedEntry, Entry
    <2> QED BY ONLY <2>1, <2>2, <2>3
<1>5. Cur(Recovered(c, selected)) \in Int
      /\ \A x \in Recovered(c, selected) : x.part \in Int /\ x.part <= Cur(Recovered(c, selected))
    BY FiniteLogPartitionFrontier, <1>1
<1>6. RecoveryCreatedEntry(c, selected) \notin Recovered(c, selected)
      /\ Count(Recovered(c, selected), RecoveryCreatedEntry(c, selected).part) = 0
    BY SMT, NewPartitionIsEmpty, <1>1, <1>4, <1>5
<1>7. BoundedLogCounts(Result(CreatedRecoveryProposal(c, selected)))
    BY SMT, AppendKeepsCountBound, <1>0, <1>1, <1>4, <1>6 DEF CreatedRecoveryProposal, Proposal, Result, Entries
<1>8. CanonicalLogShape(canonical) /\ term[c] \in Terms
    BY CandidateHasCanonicalLogShape DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>9. canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1>100. Result(CreatedRecoveryProposal(c, selected)) =
            Recovered(c, selected) \cup {RecoveryCreatedEntry(c, selected)}
    BY DEF CreatedRecoveryProposal, Proposal, Result
<1>101. term[c] \in Nat /\ \A e \in Recovered(c, selected) : e.term \in Nat
    BY ONLY SMT, <1>0, <1>1, <1>8 DEF Entries, Terms
<1>102. \A e \in Recovered(c, selected) : e.term <= term[c]
    BY ONLY SMT, <1>3, <1>101
<1>10. Result(CreatedRecoveryProposal(c, selected)) \subseteq Entries
      /\ \A e \in Result(CreatedRecoveryProposal(c, selected)) : e.term <= term[c]
    BY ONLY SMT, <1>1, <1>4, <1>100, <1>101, <1>102
<1> QED BY ReplaceCanonicalLogShape, <1>2, <1>7, <1>8, <1>9, <1>10

THEOREM CanonicalLogShapeInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ProofNext, term' \in [Replicas -> Terms]
    PROVE CanonicalLogShape(canonical')
<1>1. ProtocolNext /\ GhostNext
    BY DEF ProofNext, Next
<1>2. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryKeepsCanonicalLogShape, <1>1, <1>2
<1>3. CASE NormalCreation
    BY NormalCreationKeepsCanonicalLogShape, <1>1, <1>3 DEF NormalCreation
<1>4. CASE ~NormalCreation /\ ~\E c \in Replicas : \E selected : BuildRecovery(c, selected)
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyNormalCreationExtendsLeaderCanonical, OnlyRecoveryCreatesProposal, <1>1, <1>4
    <2>2. UNCHANGED canonical
        BY NoNewSourceKeepsCanonical, <1>1, <2>1
    <2> QED BY <2>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
        CanonicalShape, CanonicalLogShape, BoundedLogCounts
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
