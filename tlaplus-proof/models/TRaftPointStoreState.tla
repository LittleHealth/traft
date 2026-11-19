------------------------- MODULE TRaftPointStoreState ------------------------
EXTENDS TRaftClientCore

\* A mathematical interpretation of an applied set. These operators do not
\* occur in ClientAction or in the ACK-based linearization observer.
FirstRequestEntries(A) == {e \in A : e.kind = "data" /\
    ~\E f \in A : f.kind = "data" /\ f.value.id = e.value.id /\ f.part < e.part}
RequestEntries(A, id) == {e \in FirstRequestEntries(A) : e.value.id = id}
PointWrites(A, key) == {e \in FirstRequestEntries(A) :
    e.value.key = key /\ e.value.op \in {"Put", "Delete"}}
PointWritesBefore(A, key, p) == {e \in PointWrites(A, key) : e.part < p}
WriteValue(e) == IF e.value.op = "Put" THEN e.value.value ELSE Missing
LastWriteValue(W) == IF W = {} THEN Missing
    ELSE WriteValue(CHOOSE e \in W : e.part = Cur(W))
AppliedMachine(A) == [key \in Keys |-> LastWriteValue(PointWrites(A, key))]
AppliedCache(A) == [id \in RequestIds |->
    IF RequestEntries(A, id) = {} THEN [ready |-> FALSE, value |-> Missing]
    ELSE LET e == CHOOSE f \in RequestEntries(A, id) : TRUE
         IN [ready |-> TRUE,
             value |-> IF e.value.op = "Get"
                       THEN LastWriteValue(PointWritesBefore(A, e.value.key, e.part)) ELSE "OK"]]
AppliedPointState(A) == [db |-> AppliedMachine(A), cache |-> AppliedCache(A)]
ApplicationMatchesAppliedSet == \A r \in Replicas :
    machine[r] = AppliedMachine(applied[r]) /\ cache[r] = AppliedCache(applied[r])
=============================================================================
