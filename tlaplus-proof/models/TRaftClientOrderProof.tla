------------------------- MODULE TRaftClientOrderProof -----------------------
EXTENDS TRaftClientLinearizationState, SequenceTheorems, TLAPS

UniqueOrder(order) == \A i, j \in 1..Len(order) : order[i] = order[j] => i = j
OrderPrefix(a, b) == Len(a) <= Len(b) /\ \A i \in 1..Len(a) : b[i] = a[i]
RealTimeIn(events, order) == \A i, j \in 1..Len(events) :
    (i < j /\ events[i].kind = "return" /\ events[j].kind = "call"
     /\ events[i].id \in Ids(order) /\ events[j].id \in Ids(order)) =>
        Position(order, events[i].id) < Position(order, events[j].id)

THEOREM PositionHasAnActualIndex ==
    ASSUME NEW order \in Seq(RequestIds), NEW id \in Ids(order)
    PROVE Position(order, id) \in 1..Len(order) /\ order[Position(order, id)] = id
<1>1. \E i \in 1..Len(order) : order[i] = id
    BY DEF Ids
<1> QED BY ZenonT(5), <1>1 DEF Position

THEOREM UniquePositionIdentifiesIndex ==
    ASSUME NEW order \in Seq(RequestIds), UniqueOrder(order), NEW i \in 1..Len(order)
    PROVE Position(order, order[i]) = i
<1>1. order[i] \in Ids(order)
    BY DEF Ids
<1>2. Position(order, order[i]) \in 1..Len(order)
      /\ order[Position(order, order[i])] = order[i]
    BY PositionHasAnActualIndex, <1>1
<1> QED BY <1>2 DEF UniqueOrder

THEOREM PrefixKeepsPositions ==
    ASSUME NEW a \in Seq(RequestIds), NEW b \in Seq(RequestIds),
           OrderPrefix(a, b), UniqueOrder(b), NEW id \in Ids(a)
    PROVE id \in Ids(b) /\ Position(b, id) = Position(a, id)
<1>1. Position(a, id) \in 1..Len(a) /\ a[Position(a, id)] = id
      /\ Len(a) \in Nat /\ Len(b) \in Nat
    BY PositionHasAnActualIndex, LenProperties
<1>2. Position(a, id) \in 1..Len(b) /\ b[Position(a, id)] = id
    BY SMT, <1>1 DEF OrderPrefix
<1>3. Position(b, b[Position(a, id)]) = Position(a, id)
    BY UniquePositionIdentifiesIndex, <1>2
<1> QED BY <1>2, <1>3 DEF Ids

THEOREM NewIdFollowsOldPrefix ==
    ASSUME NEW a \in Seq(RequestIds), NEW b \in Seq(RequestIds),
           OrderPrefix(a, b), NEW id \in Ids(b), id \notin Ids(a)
    PROVE Len(a) < Position(b, id)
<1>1. Position(b, id) \in 1..Len(b) /\ b[Position(b, id)] = id
      /\ Len(a) \in Nat /\ Len(b) \in Nat
    BY PositionHasAnActualIndex, LenProperties
<1>2. Position(b, id) <= Len(a) => Position(b, id) \in 1..Len(a)
    BY ONLY SMT, <1>1
<1>3. Position(b, id) <= Len(a) => id \in Ids(a)
    BY <1>1, <1>2 DEF OrderPrefix, Ids
<1> QED BY SMT, <1>1, <1>3

THEOREM ExtendingWitnessPreservesRecordedRealTime ==
    ASSUME NEW E, NEW events \in Seq(E), NEW a \in Seq(RequestIds), NEW b \in Seq(RequestIds),
           OrderPrefix(a, b), UniqueOrder(b), RealTimeIn(events, a),
           \A i \in 1..Len(events) : events[i].kind = "return" => events[i].id \in Ids(a)
    PROVE RealTimeIn(events, b)
<1>1. ASSUME NEW i \in 1..Len(events), NEW j \in 1..Len(events), i < j,
            events[i].kind = "return", events[j].kind = "call",
            events[i].id \in Ids(b), events[j].id \in Ids(b)
      PROVE Position(b, events[i].id) < Position(b, events[j].id)
    <2>1. events[i].id \in Ids(a)
          /\ Position(b, events[i].id) = Position(a, events[i].id)
        BY PrefixKeepsPositions, <1>1
    <2>2. CASE events[j].id \in Ids(a)
        <3>1. Position(b, events[j].id) = Position(a, events[j].id)
            BY PrefixKeepsPositions, <2>2
        <3> QED BY <1>1, <2>1, <2>2, <3>1 DEF RealTimeIn
    <2>3. CASE events[j].id \notin Ids(a)
        <3>1. Len(a) < Position(b, events[j].id)
              /\ Position(a, events[i].id) \in 1..Len(a) /\ Len(a) \in Nat
              /\ Position(b, events[j].id) \in 1..Len(b) /\ Len(b) \in Nat
            BY NewIdFollowsOldPrefix, PositionHasAnActualIndex, LenProperties, <1>1, <2>1, <2>3
        <3> QED BY ONLY SMT, <2>1, <3>1
    <2> QED BY <2>2, <2>3
<1> QED BY <1>1 DEF RealTimeIn
=============================================================================
