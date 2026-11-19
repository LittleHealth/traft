------------------------ MODULE TRaftDurabilityState -------------------------
EXTENDS TRaftCore

StorageShape == stored = [r \in Replicas |-> stored[r]]
FormalShape == formal = [r \in Replicas |-> formal[r]]
RetainedShape == retained = [r \in Replicas |-> retained[r]]
FormalStored == \A r \in Replicas : formal[r] \subseteq stored[r]
RetainedStored == \A r \in Replicas : \A p \in retained[r] : Result(p) \subseteq stored[r]
DurableData == StorageShape /\ FormalShape /\ RetainedShape /\ FormalStored /\ RetainedStored
AckSendersValid == \A a \in ackMessages : a.sender \in Replicas
DurabilityInvariant == DurableData /\ AckSendersValid /\ AckDurability
DurabilityStep ==
    /\ DurableData'
    /\ ackMessages \subseteq ackMessages'
    /\ \A r \in Replicas : stored[r] \subseteq stored'[r]
    /\ \A a \in ackMessages' \ ackMessages :
         a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender]
=============================================================================
