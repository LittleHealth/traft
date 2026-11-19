-------------------------- MODULE TRaftEvidenceProof -------------------------
EXTENDS TRaftCore, TRaftQuorumProof, TLAPS
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM MessageAckersMonotone ==
    ASSUME NEW A, NEW B, A \subseteq B, NEW c, NEW t, NEW e
    PROVE MessageAckers(A, c, t, e) \subseteq MessageAckers(B, c, t, e)
BY SMT DEF MessageAckers

THEOREM AckQuorumMonotone ==
    ASSUME NEW A, NEW B, A \subseteq B, NEW c, NEW t, NEW e,
           Quorum(MessageAckers(A, c, t, e))
    PROVE Quorum(MessageAckers(B, c, t, e))
<1>1. MessageAckers(A, c, t, e) \subseteq MessageAckers(B, c, t, e)
    BY MessageAckersMonotone
<1>2. MessageAckers(B, c, t, e) \subseteq Replicas
    BY SMT DEF MessageAckers
<1>3. IsFiniteSet(Replicas) /\ Quorum(MessageAckers(A, c, t, e))
    BY DEF ParameterAssumptions
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, MajorityUpward DEF Quorum, Majority

THEOREM EvidenceMonotone ==
    ASSUME NEW A, NEW B, A \subseteq B
    PROVE Evidence(A) \subseteq Evidence(B)
<1>1. \A c \in Replicas, t \in Terms, e \in (UNION {a.contents : a \in A}) :
          Quorum(MessageAckers(A, c, t, e)) => Quorum(MessageAckers(B, c, t, e))
    BY SMT, AckQuorumMonotone
<1>2. (UNION {a.contents : a \in A}) \subseteq (UNION {a.contents : a \in B})
    BY SMT
<1>3. ASSUME NEW f \in Evidence(A)
      PROVE f \in Evidence(B)
    <2>1. PICK t \in Terms \ {0}, e \in (UNION {a.contents : a \in A}) :
          f = [epoch |-> t, entry |-> e] /\
          \E c \in Replicas : Quorum(MessageAckers(A, c, t, e))
        BY ONLY ZenonT(10), <1>3 DEF Evidence
    <2>2. PICK c \in Replicas : Quorum(MessageAckers(A, c, t, e))
        BY <2>1
    <2>3. e \in (UNION {a.contents : a \in B}) /\
          Quorum(MessageAckers(B, c, t, e))
        BY ONLY SMT, <1>1, <1>2, <2>1, <2>2
    <2>4. DEFINE rows == {[epoch |-> t, entry |-> x] :
              x \in {y \in (UNION {a.contents : a \in B}) :
                     \E d \in Replicas : Quorum(MessageAckers(B, d, t, y))}}
                family == {{[epoch |-> u, entry |-> x] :
                  x \in {y \in (UNION {a.contents : a \in B}) :
                         \E d \in Replicas : Quorum(MessageAckers(B, d, u, y))}} :
                    u \in Terms \ {0}}
    <2>5. f \in rows
        BY ONLY ZenonT(10), <2>1, <2>2, <2>3 DEF rows
    <2>6. rows \in family
        BY ONLY SMT, <2>1 DEF rows, family
    <2>7. f \in UNION family
        BY ONLY <2>5, <2>6
    <2> QED BY ONLY <2>7 DEF family, Evidence
<1> QED BY ONLY SMT, <1>3

THEOREM ObserverPreservesIndependentEvidence ==
    ASSUME CommitEvidenceSound, ackMessages \subseteq ackMessages', Observe
    PROVE CommitEvidenceSound'
<1>1. Evidence(ackMessages) \subseteq Evidence(ackMessages')
    BY EvidenceMonotone
<1>2. commitHistory' = commitHistory \cup Evidence(ackMessages')
      /\ commitHistory = Evidence(ackMessages)
    BY DEF Observe, CommitEvidenceSound
<1> QED BY ONLY SMT, <1>1, <1>2 DEF CommitEvidenceSound

THEOREM IndependentEvidenceHasActualDistinctSenders ==
    ASSUME NEW f \in Evidence(ackMessages)
    PROVE \E c \in Replicas :
       /\ Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
       /\ \A r \in MessageAckers(ackMessages, c, f.epoch, f.entry) :
            \E a \in ackMessages : a.sender = r /\ a.receiver = c
                        /\ a.epoch = f.epoch /\ f.entry \in a.contents
<1>1. \E c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
    BY SMT DEF Evidence
<1>2. \A c \in Replicas : \A r \in MessageAckers(ackMessages, c, f.epoch, f.entry) :
         \E a \in ackMessages : a.sender = r /\ a.receiver = c
                    /\ a.epoch = f.epoch /\ f.entry \in a.contents
    BY SMT DEF MessageAckers
<1> QED BY SMT, <1>1, <1>2

=============================================================================
