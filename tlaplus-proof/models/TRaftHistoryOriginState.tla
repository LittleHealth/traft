----------------------- MODULE TRaftHistoryOriginState -----------------------
EXTENDS TRaftCore

\* Observations only. No protocol action consults these predicates.
AppliedEvidence == \A r \in Replicas : \A e \in applied[r] :
    \E f \in commitHistory : f.entry = e
AppliedPartitionOrigins == \A h \in appliedPartitionHistory :
    /\ h.node \in Replicas /\ h.part \in Nat /\ h.entries # {}
    /\ h.entries \subseteq applied[h.node]
    /\ \A e \in h.entries : e.part = h.part
PartitionHistoryOrigins == \A h \in partitionHistory :
    /\ h.epoch \in Terms \ {0} /\ h.part \in Partitions /\ h.entries # {}
    /\ \A e \in h.entries :
          /\ e.part = h.part
          /\ \E f \in commitHistory : f.entry = e /\ f.epoch <= h.epoch
HistoryOriginInvariant == AppliedEvidence /\ AppliedPartitionOrigins /\ PartitionHistoryOrigins
=============================================================================
