----------------------- MODULE TRaftPointPartitionProof ----------------------
EXTENDS TRaftClientCore, TRaftFiniteLogProof

\* Predicates on a log, not protocol enabling conditions. Their temporal
\* establishment is a separate obligation from the algebra below.
PointLog(L) ==
    /\ \A e \in L : e.kind = "data" => e.value \in ClientCommands
    /\ \A e \in L : e.kind = "data" /\ e.value.op = "Get" => Part(L, e.part) = {e}
    /\ \A e, f \in L :
         e # f /\ e.part = f.part /\ e.kind = "data" /\ f.kind = "data" =>
           e.value.op # "Get" /\ f.value.op # "Get" /\ e.value.key # f.value.key
CanonicalPointLogs(C) == \A t \in Terms : PointLog(C[t])

THEOREM PointLogInheritedBySubset ==
    ASSUME NEW C, NEW L, PointLog(C), L \subseteq C
    PROVE PointLog(L)
BY SMT DEF PointLog, Part

THEOREM EmptyPointLog == PointLog({})
BY SMT DEF PointLog

THEOREM FreshPartitionPreservesPointLog ==
    ASSUME NEW L, PointLog(L), NEW e,
           e.kind = "data" => e.value \in ClientCommands,
           \A x \in L : x.part # e.part
    PROVE PointLog(L \cup {e})
BY SMT DEF PointLog, Part

THEOREM IndependentAppendPreservesPointLog ==
    ASSUME NEW L, PointLog(L), NEW e, e.kind = "data", e.value \in ClientCommands,
           e.value.op # "Get",
           \A x \in L : x.part = e.part /\ x.kind = "data" =>
                x.value.op # "Get" /\ x.value.key # e.value.key
    PROVE PointLog(L \cup {e})
BY SMT DEF PointLog, Part

THEOREM ClientTimestampIsNatural ==
    ASSUME NEW q \in ClientCommands
    PROVE Timestamp(q) \in Nat
<1>1. q.key \in Series \X Times
    BY DEF ClientCommands, Keys
<1>2. PICK series \in Series, instant \in Times : q.key = <<series, instant>>
    BY ONLY <1>1, Isa
<1>3. Times \subseteq Nat
    BY ClientParameters DEF ClientParameters
<1>4. q.key[2] = instant
    BY ONLY SMT, <1>2
<1> QED BY ONLY SMT, <1>2, <1>3, <1>4 DEF Timestamp

THEOREM TimedLogHasTimestampMaximum ==
    ASSUME NEW L, IsFiniteSet(L), PointLog(L), Timed(L) # {}
    PROVE MaxTimestamp(L) \in Nat
       /\ \A e \in Timed(L) : Timestamp(e.value) <= MaxTimestamp(L)
<1>1. Timed(L) \subseteq L
    BY SMT DEF Timed
<1>2. IsFiniteSet(Timed(L))
    BY FS_Subset, <1>1
<1>3. IsFiniteSet({Timestamp(e.value) : e \in Timed(L)})
    BY ONLY <1>2, FS_Image, IsaM("blast")
<1>40. \A e \in Timed(L) : e.value \in ClientCommands
    BY SMT DEF PointLog, Timed
<1>41. \A e \in Timed(L) : Timestamp(e.value) \in Nat
    BY ClientTimestampIsNatural, <1>40
<1>42. Timed(L) # {}
    OBVIOUS
<1>4. {Timestamp(e.value) : e \in Timed(L)} \subseteq Nat
      /\ {Timestamp(e.value) : e \in Timed(L)} # {}
    BY ONLY ZenonT(5), <1>41, <1>42
<1>5. MaxTimestamp(L) \in {Timestamp(e.value) : e \in Timed(L)}
      /\ \A t \in {Timestamp(e.value) : e \in Timed(L)} : t <= MaxTimestamp(L)
    BY MaxOrChoosesMaximum, <1>3, <1>4 DEF MaxTimestamp
<1> QED BY SMT, <1>4, <1>5

THEOREM OpenPartitionAdmissionIsIndependent ==
    ASSUME NEW L, IsFiniteSet(L), PointLog(L), NEW q \in ClientCommands,
           ~MustSeparate(L, q)
    PROVE q.op # "Get"
       /\ \A x \in L : x.part = Cur(L) /\ x.kind = "data" =>
              x.value.op # "Get" /\ x.value.key # q.key
<1>1. q.op # "Get" /\ ~HasRead(L) /\ ~(Timestamp(q) <= MaxTimestamp(L))
    BY DEF MustSeparate
<1>2. ASSUME NEW x \in L, x.part = Cur(L), x.kind = "data"
      PROVE x.value.op # "Get" /\ x.value.key # q.key
    <2>1. x.value.op # "Get" /\ x \in Timed(L) /\ x.value \in ClientCommands
        BY SMT, <1>1, <1>2 DEF HasRead, Timed, Part, PointLog
    <2>2. MaxTimestamp(L) \in Nat /\ Timestamp(x.value) <= MaxTimestamp(L)
        BY TimedLogHasTimestampMaximum, <2>1
    <2>3. Timestamp(x.value) \in Nat /\ Timestamp(q) \in Nat
        BY ClientTimestampIsNatural, <2>1
    <2> QED BY ONLY SMT, <1>1, <2>1, <2>2, <2>3 DEF Timestamp
<1> QED BY <1>1, <1>2

THEOREM PointPropertiesImplyClientPartitionGoals ==
    ASSUME \A r \in Replicas : PointLog(formal[r])
    PROVE ReadIsolation /\ PartitionCommandsIndependent
BY DEF PointLog, ReadIsolation, PartitionCommandsIndependent
=============================================================================
