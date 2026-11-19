------------------------ MODULE TRaftCreatedEntryProof -----------------------
EXTENDS TRaftRecoveryEpochProof
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

NormalCreatedEntry(c, v, k, successor) ==
    IF successor THEN Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]) + 1,
                            v, k, Count(formal[c], Cur(formal[c])))
    ELSE Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]),
               v, k, Count(formal[c], Cur(formal[c]) - 1))
RecoveryCreatedEntry(c, selected) ==
    Entry(LastIndex(Recovered(c, selected)) + 1, term[c], Cur(Recovered(c, selected)) + 1,
          NoValue, "noop", Count(Recovered(c, selected), Cur(Recovered(c, selected))))
CreatedRecoveryProposal(c, selected) ==
    Proposal(c, term[c], Recovered(c, selected), RecoveryCreatedEntry(c, selected), TRUE)

THEOREM FiniteSubsetCountBound ==
    ASSUME NEW C, NEW L, NEW p, IsFiniteSet(C), L \subseteq C
    PROVE Count(L, p) \in Nat /\ Count(C, p) \in Nat /\ Count(L, p) <= Count(C, p)
<1>10. Part(L, p) \subseteq Part(C, p)
    BY SMT DEF Part
<1>11. IsFiniteSet(Part(C, p)) /\ Count(C, p) \in Nat
    BY FinitePartitionCount
<1>1. Part(L, p) \subseteq Part(C, p) /\ IsFiniteSet(Part(C, p))
    BY ONLY <1>10, <1>11
<1>2. IsFiniteSet(Part(L, p)) /\ Cardinality(Part(L, p)) <= Cardinality(Part(C, p))
    BY ONLY SMT, FS_Subset, <1>1
<1> QED BY ONLY SMT, FS_CardinalityType, <1>2, <1>11 DEF Count

THEOREM FiniteLogNumericFrontier ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L)
    PROVE Cur(L) \in Int /\ LastIndex(L) \in Nat
       /\ \A x \in L : x.part \in Nat /\ x.index \in Nat
             /\ x.part <= Cur(L) /\ x.index <= LastIndex(L)
<1>1. CASE L = {}
    BY SMT, EmptyLogFrontier, <1>1
<1>2. CASE L # {}
    BY SMT, FiniteLogFrontier, <1>2 DEF Entries, Indices, Partitions
<1> QED BY <1>1, <1>2

THEOREM CanonicalSubsetHasBoundedCounts ==
    ASSUME ProofInvariant, NEW t \in Terms, NEW L, L \subseteq canonical[t], NEW p
    PROVE Count(L, p) \in 0..MaxPartitionSize
<1>00. MaxPartitionSize \in Nat
    BY DEF ParameterAssumptions
<1>1. IsFiniteSet(canonical[t]) /\ canonical[t] \subseteq Entries
      /\ \A q \in Partitions : Count(canonical[t], q) <= MaxPartitionSize
    BY DEF ProofInvariant, CanonicalFinite, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>2. Count(L, p) \in Nat /\ Count(canonical[t], p) \in Nat
      /\ Count(L, p) <= Count(canonical[t], p)
    BY FiniteSubsetCountBound, <1>1
<1>3. CASE p \in Partitions
    BY ONLY SMT, <1>00, <1>1, <1>2, <1>3
<1>4. CASE p \notin Partitions
    <2>1. Part(canonical[t], p) = {}
        BY ONLY SMT, <1>1, <1>4 DEF Part, Entries
    <2>2. Count(canonical[t], p) = 0
        BY ONLY FS_EmptySet, <2>1 DEF Count
    <2> QED BY SMT, <1>2, <2>2
<1> QED BY <1>3, <1>4

THEOREM NormalCreationIsTypedAndCoherent ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE NormalCreatedEntry(c, v, k, successor) \in Entries
       /\ Coherent(formal[c] \cup {NormalCreatedEntry(c, v, k, successor)})
<1>1. role[c] = "Leader" /\ term[c] \in Terms \ {0}
      /\ formal[c] = canonical[term[c]] /\ formal[c] \subseteq Entries
      /\ IsFiniteSet(formal[c]) /\ Coherent(formal[c]) /\ formal[c] # {}
    BY SMT DEF CreateEntry, CreateSuccessor, Aligned, ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, TypeOK, CanonicalShape, ElectionInvariant, ElectionTypes,
       FiniteLogInvariant, FiniteNodeData
<1>2. Cur(formal[c]) \in Nat /\ LastIndex(formal[c]) \in Nat
      /\ (\A x \in formal[c] : x.part <= Cur(formal[c]) /\ x.index <= LastIndex(formal[c]))
      /\ (\E x \in formal[c] : x.part = Cur(formal[c]))
    BY FiniteLogFrontier, <1>1
<1>20. \A x \in formal[c] : x.part \in Nat /\ x.index \in Nat
    BY ONLY SMT, <1>1 DEF Entries, Indices, Partitions
<1>3. Cur(formal[c]) \in Partitions
    BY SMT, <1>1, <1>2 DEF Entries
<1>4. Count(formal[c], Cur(formal[c])) \in 0..MaxPartitionSize
      /\ Count(formal[c], Cur(formal[c]) - 1) \in 0..MaxPartitionSize
    BY CanonicalSubsetHasBoundedCounts, <1>1
<1>5. NormalCreatedEntry(c, v, k, successor) \in Entries
      /\ ((NormalCreatedEntry(c, v, k, successor).kind = "noop")
           <=> (NormalCreatedEntry(c, v, k, successor).value = NoValue))
    BY SMT, <1>1, <1>2, <1>3, <1>4 DEF NormalCreatedEntry, Entry, Entries, CreateEntry, CreateSuccessor
<1>50. NormalCreatedEntry(c, v, k, successor).index = LastIndex(formal[c]) + 1
      /\ NormalCreatedEntry(c, v, k, successor).part = Cur(formal[c]) + (IF successor THEN 1 ELSE 0)
      /\ NormalCreatedEntry(c, v, k, successor).term = term[c]
    BY SMT, <1>2 DEF NormalCreatedEntry, Entry
<1>6. CASE successor
    <2>1. \A x \in formal[c] : x.index < NormalCreatedEntry(c, v, k, successor).index
              /\ x.part < NormalCreatedEntry(c, v, k, successor).part
        BY ONLY SMT, <1>2, <1>20, <1>50, <1>6
    <2> QED BY CoherentNewPartition, <1>1, <1>5, <2>1
<1>7. CASE ~successor
    <2>1. Origin(formal[c], Cur(formal[c])) = term[c] /\ Part(formal[c], Cur(formal[c])) # {}
        BY SMT, <1>2, <1>7 DEF CreateEntry, Part
    <2>2. PICK originEntry \in Part(formal[c], Cur(formal[c])) : originEntry.term = term[c]
        BY ZenonT(5), <2>1 DEF Origin
    <2>3. \A x \in formal[c] : x.part = Cur(formal[c]) => x.term = term[c]
        BY SMT, <1>1, <2>2 DEF Coherent, Part
    <2>4. \A x \in formal[c] : x.index < NormalCreatedEntry(c, v, k, successor).index
              /\ x.part <= NormalCreatedEntry(c, v, k, successor).part
        BY ONLY SMT, <1>2, <1>20, <1>50, <1>7
    <2>5. \A x \in formal[c] : x.part = NormalCreatedEntry(c, v, k, successor).part
              => x.term = NormalCreatedEntry(c, v, k, successor).term
        BY ONLY SMT, <1>2, <1>50, <1>7, <2>3
    <2> QED BY CoherentOpenPartitionExtension, <1>1, <1>5, <2>4, <2>5
<1> QED BY <1>6, <1>7

THEOREM EmptyReportRecoveryHasNoInput ==
    ASSUME NEW c \in Replicas, NEW selected, BuildRecovery(c, selected), ReportedProposals(c) = {}
    PROVE selected = NoProposal /\ Recovered(c, selected) = {}
<1>1. selected = NoProposal
    BY DEF BuildRecovery
<1> QED BY ONLY <1>1 DEF Recovered

THEOREM SelectedRecoveryProposalIsActual ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected,
           BuildRecovery(c, selected), ReportedProposals(c) # {}
    PROVE selected \in Latest(ReportedProposals(c)) /\ selected \in proposals /\ selected.epoch \in Terms
<1>1. selected \in Latest(ReportedProposals(c)) /\ selected \in ReportedProposals(c)
    BY DEF BuildRecovery, Latest
<1>2. ReportedProposals(c) \subseteq proposals
    BY ReportedProposalsAreActual
<1>3. \A p \in proposals : p.epoch \in Terms
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1> QED BY ONLY ZenonT(5), <1>1, <1>2, <1>3

THEOREM RecoveryInputIsFiniteTypedAndCoherent ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE Recovered(c, selected) \subseteq Entries /\ IsFiniteSet(Recovered(c, selected))
          /\ Coherent(Recovered(c, selected))
<1>1. CASE ReportedProposals(c) = {}
    <2>1. Recovered(c, selected) = {}
        BY EmptyReportRecoveryHasNoInput, <1>1
    <2> QED BY ONLY SMT, FS_EmptySet, <2>1 DEF Coherent
<1>2. CASE ReportedProposals(c) # {}
    <2>1. selected \in Latest(ReportedProposals(c)) /\ selected \in proposals
          /\ selected.epoch \in Terms
        BY SelectedRecoveryProposalIsActual, <1>2
    <2>2. Recovered(c, selected) \subseteq canonical[selected.epoch]
        BY RecoveredIsCanonicalSubset, <2>1
    <2>3. canonical[selected.epoch] \subseteq Entries /\ IsFiniteSet(canonical[selected.epoch])
          /\ Coherent(canonical[selected.epoch])
        BY <2>1 DEF ProofInvariant, CanonicalFinite, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2> QED BY CoherenceInheritedBySubset, FS_Subset, <2>2, <2>3
<1> QED BY <1>1, <1>2

THEOREM RecoveryCreationIsTypedAndCoherent ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CreatedRecoveryProposal(c, selected) \in ProposalRecords
          /\ Coherent(Result(CreatedRecoveryProposal(c, selected)))
<1>1. Recovered(c, selected) \subseteq Entries /\ IsFiniteSet(Recovered(c, selected))
          /\ Coherent(Recovered(c, selected))
    BY RecoveryInputIsFiniteTypedAndCoherent
<1>2. term[c] \in Terms \ {0}
    BY SMT DEF BuildRecovery, ProofInvariant, PreProvenanceInvariant, ElectionInvariant, ElectionTypes
<1>3. Count(Recovered(c, selected), Cur(Recovered(c, selected))) \in Nat
    BY FinitePartitionCount, <1>1
<1>4. RecoveryCreatedEntry(c, selected) \in Entries
    BY SMT, <1>2, <1>3 DEF BuildRecovery, RecoveryCreatedEntry, Entry, Entries
<1>50. Cur(Recovered(c, selected)) \in Int /\ LastIndex(Recovered(c, selected)) \in Nat
      /\ \A x \in Recovered(c, selected) : x.part \in Nat /\ x.index \in Nat
           /\ x.part <= Cur(Recovered(c, selected)) /\ x.index <= LastIndex(Recovered(c, selected))
    BY FiniteLogNumericFrontier, <1>1
<1>51. RecoveryCreatedEntry(c, selected).index = LastIndex(Recovered(c, selected)) + 1
      /\ RecoveryCreatedEntry(c, selected).part = Cur(Recovered(c, selected)) + 1
    BY SMT DEF RecoveryCreatedEntry, Entry
<1>5. \A x \in Recovered(c, selected) :
          x.index < RecoveryCreatedEntry(c, selected).index
          /\ x.part < RecoveryCreatedEntry(c, selected).part
    BY ONLY SMT, <1>50, <1>51
<1>6. Coherent(Recovered(c, selected) \cup {RecoveryCreatedEntry(c, selected)})
    BY CoherentNewPartition, <1>1, <1>4, <1>5 DEF RecoveryCreatedEntry, Entry
<1> QED BY SMT, <1>1, <1>2, <1>4, <1>6 DEF CreatedRecoveryProposal, Proposal, ProposalRecords, Result
=============================================================================
