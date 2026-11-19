-------------------- MODULE TRaftEvidenceBatchInterpretation -----------------
EXTENDS TRaftOrderedApplicationProof, TRaftWitnessFold

EntryRequestIds(A) == {e.value.id : e \in {x \in A : x.kind = "data"}}
FreshEvidenceBatch(A, B) == {e \in B : e.kind = "data" /\ e.value.id \notin EntryRequestIds(A)}

THEOREM EarlierRepresentativesPreserveFirstOccurrences ==
    ASSUME RequestIdentityState, NEW B, B \subseteq Entries, PointLog(B),
           \A e \in B : e.kind = "data" => e.value \in calls,
           NEW A, A \subseteq B,
           \A e \in B : e.kind = "data" =>
             \E f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part <= e.part
    PROVE FirstRequestEntries(A) = FirstRequestEntries(B)
<1>1. ASSUME NEW e \in FirstRequestEntries(B)
      PROVE e \in FirstRequestEntries(A)
    <2>1. e \in B /\ e.kind = "data" /\ e.part \in Int
        BY <1>1 DEF FirstRequestEntries, Entries, Partitions
    <2>2. PICK f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part <= e.part
        BY <2>1
    <2>3. f \in B /\ f.part \in Int /\ ~(f.part < e.part)
        BY <1>1, <2>2 DEF FirstRequestEntries, Entries, Partitions
    <2>4. f.part = e.part
        BY ONLY SMT, <2>1, <2>2, <2>3
    <2>5. f = e
        BY SameRequestInOnePartitionIsOneEntry, <2>1, <2>2, <2>3, <2>4
    <2> QED BY <1>1, <2>2, <2>5 DEF FirstRequestEntries
<1>2. ASSUME NEW e \in FirstRequestEntries(A)
      PROVE e \in FirstRequestEntries(B)
    <2>1. e \in A /\ e \in B /\ e.kind = "data" /\ e.part \in Int
        BY <1>2 DEF FirstRequestEntries, Entries, Partitions
    <2>2. ASSUME NEW g \in B, g.kind = "data", g.value.id = e.value.id, g.part < e.part
          PROVE FALSE
        <3>1. PICK f \in A : f.kind = "data" /\ f.value.id = g.value.id /\ f.part <= g.part
            BY <2>2
        <3>2. f.part \in Int /\ g.part \in Int /\ f.part < e.part
            BY SMT, <2>1, <2>2, <3>1 DEF Entries, Partitions
        <3> QED BY <1>2, <2>2, <3>1, <3>2 DEF FirstRequestEntries
    <2> QED BY <2>1, <2>2 DEF FirstRequestEntries
<1> QED BY <1>1, <1>2

THEOREM FreshBatchHasAllNecessaryFirstOccurrences ==
    ASSUME RequestIdentityState, NEW B, B \subseteq Entries, PointLog(B),
           \A e \in B : e.kind = "data" => e.value \in calls,
           NEW A, A \subseteq B,
           \A e \in B \ A : \A old \in A : old.part <= e.part
    PROVE FirstRequestEntries(A \cup FreshEvidenceBatch(A, B)) = FirstRequestEntries(B)
<1>1. A \cup FreshEvidenceBatch(A, B) \subseteq B
    BY DEF FreshEvidenceBatch
<1>2. ASSUME NEW e \in B, e.kind = "data"
      PROVE \E f \in A \cup FreshEvidenceBatch(A, B) :
          f.kind = "data" /\ f.value.id = e.value.id /\ f.part <= e.part
    <2>1. e.part \in Int
        BY DEF Entries, Partitions
    <2>2. CASE e \in A \cup FreshEvidenceBatch(A, B)
        BY SMT, <1>2, <2>1, <2>2
    <2>3. CASE e \notin A \cup FreshEvidenceBatch(A, B)
        <3>1. e \in B \ A /\ e.value.id \in EntryRequestIds(A)
            BY <1>2, <2>3 DEF FreshEvidenceBatch
        <3>2. PICK f \in A : f.kind = "data" /\ f.value.id = e.value.id
            BY <3>1 DEF EntryRequestIds
        <3>3. f.part <= e.part
            BY <3>1, <3>2
        <3> QED BY <3>2, <3>3
    <2> QED BY <2>2, <2>3
<1> QED BY EarlierRepresentativesPreserveFirstOccurrences, <1>1, <1>2

THEOREM SortedCoherentEntriesFollowPartitionOrder ==
    ASSUME NEW S, IsFiniteSet(S), S \subseteq Entries, Coherent(S)
    PROVE Enumerates(SortedEntryOrder(S), S) /\ PartitionOrdered(SortedEntryOrder(S))
<1>1. SortedEntryOrder(S) \in EntryOrders(S)
    BY SortedEntryOrderExists
<1>2. Enumerates(SortedEntryOrder(S), S) /\ IncreasingEntryOrder(SortedEntryOrder(S))
    BY <1>1 DEF EntryOrders
<1>3. \A i \in 1..Len(SortedEntryOrder(S)) : SortedEntryOrder(S)[i] \in S
    BY <1>2 DEF Enumerates, SequenceEntries
<1> QED BY <1>2, <1>3 DEF PartitionOrdered, IncreasingEntryOrder, Coherent

THEOREM FreshBatchHasSequentialApplicationInterpretation ==
    ASSUME RequestIdentityState, NEW B, IsFiniteSet(B), B \subseteq Entries, PointLog(B), Coherent(B),
           \A e \in B : e.kind = "data" => e.value \in calls,
           NEW A, A \subseteq B,
           \A e \in B \ A : \A old \in A : old.part <= e.part
    PROVE Fold(SortedEntryOrder(FreshEvidenceBatch(A, B)), AppliedPointState(A), EntryPointStep)
             = AppliedPointState(B)
<1>1. DEFINE S == FreshEvidenceBatch(A, B)
<1>2. S \subseteq B /\ A \cap S = {} /\ A \cup S \subseteq B
      /\ \A old \in A, e \in S : old.part <= e.part
    BY DEF S, FreshEvidenceBatch, EntryRequestIds
<1>3. IsFiniteSet(A) /\ IsFiniteSet(S) /\ A \subseteq Entries /\ S \subseteq Entries
      /\ Coherent(S) /\ PointLog(A \cup S)
    BY FS_Subset, PointLogInheritedBySubset, <1>2 DEF Coherent
<1>4. Enumerates(SortedEntryOrder(S), S) /\ PartitionOrdered(SortedEntryOrder(S))
    BY SortedCoherentEntriesFollowPartitionOrder, <1>3
<1>5. Fold(SortedEntryOrder(S), AppliedPointState(A), EntryPointStep) = AppliedPointState(A \cup S)
    BY OrderedFoldHasAppliedSetInterpretation, <1>2, <1>3, <1>4
<1>6. FirstRequestEntries(A \cup S) = FirstRequestEntries(B)
    BY FreshBatchHasAllNecessaryFirstOccurrences DEF S
<1>7. AppliedPointState(A \cup S) = AppliedPointState(B)
    BY SameFirstRequestsDetermineSamePointState, <1>6
<1> QED BY <1>5, <1>7 DEF S

THEOREM EvidenceBatchExtendsTheSequentialWitness ==
    ASSUME RequestIdentityState, NEW B, IsFiniteSet(B), B \subseteq Entries, PointLog(B), Coherent(B),
           \A e \in B : e.kind = "data" => e.value \in calls,
           NEW A, A \subseteq B,
           \A e \in B \ A : \A old \in A : old.part <= e.part,
           NEW initial \in WitnessStates, UniqueOrder(initial.order), WitnessSequential(initial),
           WitnessPoint(initial) = AppliedPointState(A)
    PROVE LET result == Fold(SortedEntryOrder(FreshEvidenceBatch(A, B)), initial, LinearizationEntryStep)
          IN /\ result \in WitnessStates /\ UniqueOrder(result.order)
             /\ OrderPrefix(initial.order, result.order) /\ WitnessSequential(result)
             /\ WitnessPoint(result) = AppliedPointState(B)
             /\ Ids(result.order) = EntryRequestIds(B)
<1>1. DEFINE S == FreshEvidenceBatch(A, B)
            order == SortedEntryOrder(S)
            result == Fold(order, initial, LinearizationEntryStep)
<1>2. S \subseteq B /\ IsFiniteSet(S) /\ S \subseteq Entries /\ Coherent(S)
      /\ \A e \in S : e.kind = "data" /\ e.value \in calls /\ e.value \in ClientCommands
    BY FS_Subset DEF S, FreshEvidenceBatch, Coherent, RequestIdentityState
<1>3. order \in Seq(S)
    BY SortedCoherentEntriesFollowPartitionOrder, <1>2 DEF order, Enumerates
<1>4. result \in WitnessStates /\ UniqueOrder(result.order)
      /\ OrderPrefix(initial.order, result.order) /\ WitnessSequential(result)
    BY FoldingEvidenceKeepsSequentialWitness, <1>2, <1>3 DEF result
<1>5. WitnessPoint(result) = Fold(order, AppliedPointState(A), EntryPointStep)
    BY FoldingEvidenceSimulatesApplication, <1>2, <1>3 DEF result
<1>6. WitnessPoint(result) = AppliedPointState(B)
    BY FreshBatchHasSequentialApplicationInterpretation, <1>5 DEF order, S
<1>7. Ids(result.order) = EntryRequestIds(B)
    BY WitnessInterpretationDeterminesIdentitySet, <1>4, <1>6 DEF EntryRequestIds, RequestIdentityState
<1> QED BY <1>4, <1>6, <1>7 DEF S, order, result
=============================================================================
