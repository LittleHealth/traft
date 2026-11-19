------------------------- MODULE TRaftFoldConcatProof ------------------------
EXTENDS TRaftSequenceFoldProof

THEOREM FoldEmptySequence ==
    ASSUME NEW initial, NEW Step(_, _)
    PROVE Fold(<<>>, initial, Step) = initial
<1>1. Len(<<>>) = 0
    BY EmptySeq
<1> QED BY FoldTraceStartsAtInitial, <1>1 DEF Fold

THEOREM ConcatenationCommutesWithAppend ==
    ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW e \in S
    PROVE a \o Append(b, e) = Append(a \o b, e)
<1>1. <<e>> \in Seq(S) /\ a \o b \in Seq(S)
    BY SMT, ConcatProperties
<1>2. Append(b, e) = b \o <<e>> /\ Append(a \o b, e) = (a \o b) \o <<e>>
    BY AppendIsConcat, <1>1
<1> QED BY ConcatAssociative, <1>1, <1>2

THEOREM FoldConcatenation ==
    ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), NEW initial, NEW Step(_, _)
    PROVE Fold(a \o b, initial, Step) = Fold(b, Fold(a, initial, Step), Step)
<1>1. DEFINE P(t) == Fold(a \o t, initial, Step) = Fold(t, Fold(a, initial, Step), Step)
<1>2. P(<<>>)
    BY FoldEmptySequence, ConcatEmptySeq DEF P
<1>3. ASSUME NEW t \in Seq(S), NEW e \in S, P(t)
      PROVE P(Append(t, e))
    <2>1. a \o t \in Seq(S) /\ a \o Append(t, e) = Append(a \o t, e)
        BY ConcatProperties, ConcatenationCommutesWithAppend
    <2>2. Fold(Append(a \o t, e), initial, Step) = Step(Fold(a \o t, initial, Step), e)
          /\ Fold(Append(t, e), Fold(a, initial, Step), Step)
               = Step(Fold(t, Fold(a, initial, Step), Step), e)
        BY FoldAppend, <2>1
    <2> QED BY <1>3, <2>1, <2>2 DEF P
<1> HIDE DEF P
<1>4. \A t \in Seq(S) : P(t)
    BY ONLY SequencesInductionAppend, <1>2, <1>3, IsaM("blast")
<1> QED BY <1>4 DEF P
=============================================================================
