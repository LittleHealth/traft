------------------------- MODULE TRaftEntryOrderState -------------------------
EXTENDS TRaftCore, Sequences

SequenceEntries(order) == {order[i] : i \in 1..Len(order)}
Enumerates(order, S) ==
    /\ order \in Seq(S)
    /\ SequenceEntries(order) = S
    /\ \A i, j \in 1..Len(order) : order[i] = order[j] => i = j
IncreasingEntryOrder(order) == \A i, j \in 1..Len(order) :
    i < j => order[i].index < order[j].index
EntryOrders(S) == {order \in [1..Cardinality(S) -> S] :
    Enumerates(order, S) /\ IncreasingEntryOrder(order)}
SortedEntryOrder(S) == CHOOSE order \in EntryOrders(S) : TRUE
=============================================================================
