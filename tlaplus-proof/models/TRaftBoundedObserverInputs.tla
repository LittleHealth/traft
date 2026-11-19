---------------------- MODULE TRaftBoundedObserverInputs ---------------------
EXTENDS TRaftBoundedActionInstances, TRaftCommitSupport,
        TRaftObserverClosureProof, TRaftEpochClosureProof

EvidenceIn(M, U) == (UNION {EpochEvidence(M, t) : t \in U})
UnboundedClosed == (UNION {
    {[epoch |-> term[r], part |-> q, entries |-> Part(formal[r], q)] :
       q \in {j \in Nat : j < Cur(formal[r]) /\ Part(formal[r], j) # {}}} : r \in Replicas})

THEOREM EvidenceEpochComesFromAnAck ==
    ASSUME NEW M, NEW t, NEW e \in EpochEvidence(M, t)
    PROVE \E a \in M : a.epoch = t
<1>1. PICK x \in (UNION {a.contents : a \in M}), c \in Replicas :
          Quorum(MessageAckers(M, c, t, x))
    BY DEF EpochEvidence
<1>2. MessageAckers(M, c, t, x) # {}
    BY QuorumIsNonempty, <1>1
<1> QED BY <1>2 DEF MessageAckers

THEOREM ExtendingEpochDomainAddsNoEvidence ==
    ASSUME NEW M, NEW U, NEW V, U \subseteq V, \A a \in M : a.epoch \in U
    PROVE EvidenceIn(M, U) = EvidenceIn(M, V)
<1>1. EvidenceIn(M, U) \subseteq EvidenceIn(M, V)
    BY ZenonT(5) DEF EvidenceIn
<1>2. ASSUME NEW e \in EvidenceIn(M, V)
      PROVE e \in EvidenceIn(M, U)
    <2>1. PICK t \in V : e \in EpochEvidence(M, t)
        BY <1>2 DEF EvidenceIn
    <2>2. PICK a \in M : a.epoch = t
        BY EvidenceEpochComesFromAnAck, <2>1
    <2>3. t \in U
        BY <2>2
    <2> QED BY <2>1, <2>3 DEF EvidenceIn
<1> QED BY <1>1, <1>2

THEOREM BoundedAndUnboundedEvidenceIdentities ==
    ASSUME NEW M
    PROVE Evidence(M) = EvidenceIn(M, Terms \ {0})
          /\ Infinite!Evidence(M) = EvidenceIn(M, Nat \ {0})
<1>01. \A S : Infinite!IsFiniteSet(S) = IsFiniteSet(S)
    BY ONLY ZenonT(10) DEF Infinite!IsFiniteSet, IsFiniteSet
<1>1. \A S : Infinite!Cardinality(S) = Cardinality(S)
    BY ONLY ZenonT(10), <1>01 DEF Infinite!Cardinality, Cardinality
<1>2. Infinite!Terms = Nat
    BY ONLY SMT DEF Infinite!Terms
<1>3. \A c, t, e : Infinite!MessageAckers(M, c, t, e) = MessageAckers(M, c, t, e)
    BY ONLY DEF Infinite!MessageAckers, MessageAckers
<1>4. \A Q : Infinite!Quorum(Q) = Quorum(Q)
    BY ONLY <1>1 DEF Infinite!Quorum, Quorum
<1>5. Evidence(M) = EvidenceIn(M, Terms \ {0})
    BY ONLY DEF EvidenceIn, EpochEvidence, Evidence
<1>6. Infinite!Evidence(M) = EvidenceIn(M, Nat \ {0})
    BY ONLY <1>2, <1>3, <1>4 DEF EvidenceIn, EpochEvidence, Infinite!Evidence
<1> QED BY ONLY <1>5, <1>6

THEOREM BoundedAcksHaveTheSameUnboundedEvidence ==
    ASSUME NEW M, \A a \in M : a.epoch \in Terms \ {0}
    PROVE Evidence(M) = Infinite!Evidence(M)
<1>1. Terms \ {0} \subseteq Nat \ {0}
    BY SMT DEF Terms
<1>2. EvidenceIn(M, Terms \ {0}) = EvidenceIn(M, Nat \ {0})
    BY ExtendingEpochDomainAddsNoEvidence, <1>1
<1> QED BY BoundedAndUnboundedEvidenceIdentities, <1>2

THEOREM NonemptyPartHasAnEntryInThatPartition ==
    ASSUME NEW L, L \subseteq Entries, NEW q, Part(L, q) # {}
    PROVE q \in Partitions
BY DEF Part, Entries

THEOREM RemovingPartitionBoundAddsNoClosedLog ==
    (formal \in [Replicas -> SUBSET Entries]) => PresentClosed = UnboundedClosed
<1>0. SUFFICES ASSUME formal \in [Replicas -> SUBSET Entries]
              PROVE PresentClosed = UnboundedClosed
    OBVIOUS
<1>1. \A r \in Replicas : \A q : Part(formal[r], q) # {} => q \in Partitions
    <2>1. ASSUME NEW r \in Replicas, NEW q, Part(formal[r], q) # {}
          PROVE q \in Partitions
        <3>1. formal[r] \subseteq Entries
            BY ONLY SMT, <1>0, <2>1
        <3> QED BY ONLY NonemptyPartHasAnEntryInThatPartition, <2>1, <3>1
    <2> QED BY ONLY <2>1
<1>2. Partitions \subseteq Nat
    BY SMT DEF Partitions
<1>3. ASSUME NEW x \in PresentClosed
      PROVE x \in UnboundedClosed
    <2>1. PICK r \in Replicas, q \in Partitions :
              q < Cur(formal[r]) /\ Part(formal[r], q) # {}
              /\ x = [epoch |-> term[r], part |-> q, entries |-> Part(formal[r], q)]
        BY ONLY ZenonT(5), <1>3 DEF PresentClosed
    <2>2. q \in Nat
        BY ONLY <1>2, <2>1
    <2>3. DEFINE rows ==
              {[epoch |-> term[r], part |-> j, entries |-> Part(formal[r], j)] :
                 j \in {k \in Nat : k < Cur(formal[r]) /\ Part(formal[r], k) # {}}}
                family ==
              {{[epoch |-> term[s], part |-> j, entries |-> Part(formal[s], j)] :
                  j \in {k \in Nat : k < Cur(formal[s]) /\ Part(formal[s], k) # {}}} :
                 s \in Replicas}
    <2>4. q \in {k \in Nat : k < Cur(formal[r]) /\ Part(formal[r], k) # {}}
        BY ONLY SMT, <2>1, <2>2
    <2>5. x \in rows
        BY ONLY SMT, <2>1, <2>4 DEF rows
    <2>6. rows \in family
        BY ONLY SMT, <2>1 DEF rows, family
    <2>7. x \in UNION family
        BY ONLY <2>5, <2>6
    <2> QED BY ONLY <2>7 DEF family, UnboundedClosed
<1>4. ASSUME NEW x \in UnboundedClosed
      PROVE x \in PresentClosed
    <2>1. PICK r \in Replicas, q \in Nat :
              q < Cur(formal[r]) /\ Part(formal[r], q) # {}
              /\ x = [epoch |-> term[r], part |-> q, entries |-> Part(formal[r], q)]
        BY ONLY ZenonT(5), <1>4 DEF UnboundedClosed
    <2>2. q \in Partitions
        BY ONLY <1>1, <2>1
    <2>3. DEFINE rows ==
              {[epoch |-> term[r], part |-> j, entries |-> Part(formal[r], j)] :
                 j \in {k \in Partitions : k < Cur(formal[r]) /\ Part(formal[r], k) # {}}}
                family ==
              {{[epoch |-> term[s], part |-> j, entries |-> Part(formal[s], j)] :
                  j \in {k \in Partitions : k < Cur(formal[s]) /\ Part(formal[s], k) # {}}} :
                 s \in Replicas}
    <2>4. q \in {k \in Partitions : k < Cur(formal[r]) /\ Part(formal[r], k) # {}}
        BY ONLY SMT, <2>1, <2>2
    <2>5. x \in rows
        BY ONLY SMT, <2>1, <2>4 DEF rows
    <2>6. rows \in family
        BY ONLY SMT, <2>1 DEF rows, family
    <2>7. x \in UNION family
        BY ONLY <2>5, <2>6
    <2> QED BY ONLY <2>7 DEF family, PresentClosed
<1> QED BY ONLY <1>3, <1>4

THEOREM ClosedLogEpochsAndEvidenceEpochsAreBounded ==
    (MaxTerm \in Nat \ {0} /\ term \in [Replicas -> Terms]
     /\ commitHistory = Evidence(ackMessages)) =>
      (\A v \in PresentClosed : v.epoch \in 0..MaxTerm)
      /\ (\A f \in commitHistory : f.epoch \in 0..MaxTerm)
BY SMT DEF PresentClosed, Evidence, Terms

THEOREM PresentPartitionHistoryIsCertification ==
    PresentPartitions = CertifiedClosed(PresentClosed, commitHistory, Terms \ {0})
BY DEF PresentPartitions, CertifiedClosed

THEOREM BoundedPartitionHistoryGrowthEmbeds ==
    ASSUME MaxTerm \in Nat \ {0}, term' \in [Replicas -> Terms],
           formal' \in [Replicas -> SUBSET Entries], CommitEvidenceSound', Observe
    PROVE EpochClosure(partitionHistory') = EpochClosure(partitionHistory) \cup
            CertifiedClosed(UnboundedClosed', commitHistory', Nat \ {0})
<1>0. RemovingPartitionBoundAddsNoClosedLog'
      /\ ClosedLogEpochsAndEvidenceEpochsAreBounded'
      /\ PresentPartitionHistoryIsCertification'
    BY ONLY PTL, RemovingPartitionBoundAddsNoClosedLog,
       ClosedLogEpochsAndEvidenceEpochsAreBounded, PresentPartitionHistoryIsCertification
<1>1. Terms = 0..MaxTerm /\ Terms \ {0} = 1..MaxTerm
    BY SMT DEF Terms
<1>2. PresentClosed' = UnboundedClosed'
      /\ (\A v \in PresentClosed' : v.epoch \in 0..MaxTerm)
      /\ (\A f \in commitHistory' : f.epoch \in 0..MaxTerm)
    BY <1>0, <1>1 DEF CommitEvidenceSound
<1>3. partitionHistory' = partitionHistory \cup
          CertifiedClosed(PresentClosed', commitHistory', 1..MaxTerm)
    BY ObserveHasEquations, <1>0, <1>1 DEF ObservationEquations
<1>4. EpochClosure(partitionHistory \cup CertifiedClosed(PresentClosed', commitHistory', 1..MaxTerm))
          = EpochClosure(partitionHistory) \cup CertifiedClosed(PresentClosed', commitHistory', Nat \ {0})
    BY EpochClosureCommutesWithHistoryGrowth, <1>2
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
