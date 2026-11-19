------------------------ MODULE TRaftDurabilityProof -------------------------
EXTENDS TRaftDurabilityState, TRaftEvidenceProof, TRaftFunctionProof, TLAPS

THEOREM EveryStepPreservesDurabilityFacts ==
    ASSUME DurableData, ProtocolNext
    PROVE DurabilityStep
<1>1. \A c \in Replicas : StartElection(c) => DurabilityStep
    BY SMT DEF StartElection, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>2. \A r \in Replicas : \A t : AdoptTerm(r, t) => DurabilityStep
    BY SMT DEF AdoptTerm, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>3. \A r \in Replicas : \A req : GrantVote(r, req) => DurabilityStep
    BY SMT DEF GrantVote, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>4. \A c \in Replicas : \A m : DeliverVote(c, m) => DurabilityStep
    BY SMT DEF DeliverVote, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>5. \A c \in Replicas : WinElection(c) => DurabilityStep
    BY SMT DEF WinElection, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>6. \A r \in Replicas : \A req : MakeReport(r, req) => DurabilityStep
    BY SMT DEF MakeReport, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>7. \A c \in Replicas : \A m : DeliverReport(c, m) => DurabilityStep
    BY SMT DEF DeliverReport, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>8. ASSUME NEW c \in Replicas, NEW p, BuildRecovery(c, p)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        <3>1. StorageShape'
            <4>1. stored = [r \in Replicas |-> stored[r]] /\ c \in Replicas
                BY <1>8 DEF DurableData, StorageShape
            <4>2. stored' = [stored EXCEPT ![c] = @ \cup
                         {Entry(LastIndex(Recovered(c, p)) + 1, term[c], Cur(Recovered(c, p)) + 1,
                         NoValue, "noop", Count(Recovered(c, p), Cur(Recovered(c, p))))}]
                BY <1>8 DEF BuildRecovery
            <4> QED BY ONLY FunctionUpdatePreservesDomainShape, <4>1, <4>2 DEF StorageShape
        <3>2. FormalShape'
            BY SMT, <1>8, FunctionUpdatePreservesDomainShape DEF DurableData, FormalShape, BuildRecovery
        <3>3. RetainedShape'
            BY SMT, <1>8 DEF DurableData, RetainedShape, BuildRecovery
        <3> QED BY <3>1, <3>2, <3>3
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>8 DEF BuildRecovery, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>8 DEF BuildRecovery, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>8, <2>2 DEF BuildRecovery, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>9. ASSUME NEW c \in Replicas, NEW v, CreateEntry(c, v)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        <3>1. StorageShape'
            <4>1. stored = [r \in Replicas |-> stored[r]] /\ c \in Replicas
                BY <1>9 DEF DurableData, StorageShape
            <4>2. stored' = [stored EXCEPT ![c] = @ \cup
                         {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]), v, "data",
                         Count(formal[c], Cur(formal[c]) - 1))}]
                BY <1>9 DEF CreateEntry
            <4> QED BY ONLY FunctionUpdatePreservesDomainShape, <4>1, <4>2 DEF StorageShape
        <3>2. FormalShape'
            <4>1. formal = [r \in Replicas |-> formal[r]] /\ c \in Replicas
                BY <1>9 DEF DurableData, FormalShape
            <4>2. formal' = [formal EXCEPT ![c] = @ \cup
                         {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]), v, "data",
                         Count(formal[c], Cur(formal[c]) - 1))}]
                BY <1>9 DEF CreateEntry
            <4> QED BY ONLY FunctionUpdatePreservesDomainShape, <4>1, <4>2 DEF FormalShape
        <3>3. RetainedShape'
            BY SMT, <1>9 DEF DurableData, RetainedShape, CreateEntry
        <3> QED BY <3>1, <3>2, <3>3
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>9 DEF CreateEntry, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>9 DEF CreateEntry, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>9, <2>2 DEF CreateEntry, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>10. ASSUME NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        <3>1. StorageShape'
            BY SMT, <1>10, FunctionUpdatePreservesDomainShape DEF DurableData, StorageShape, CreateSuccessor
        <3>2. FormalShape'
            BY SMT, <1>10, FunctionUpdatePreservesDomainShape DEF DurableData, FormalShape, CreateSuccessor
        <3>3. RetainedShape'
            BY SMT, <1>10 DEF DurableData, RetainedShape, CreateSuccessor
        <3> QED BY <3>1, <3>2, <3>3
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>10 DEF CreateSuccessor, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>10 DEF CreateSuccessor, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>10, <2>2 DEF CreateSuccessor, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>11. \A c \in Replicas : \A e : SendEntry(c, e) => DurabilityStep
    BY SMT DEF SendEntry, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>12. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        <3>1. StorageShape'
            BY SMT, <1>12, FunctionUpdatePreservesDomainShape DEF DurableData, StorageShape, ReceiveEntry
        <3>2. FormalShape'
            BY SMT, <1>12, FunctionUpdatePreservesDomainShape DEF DurableData, FormalShape, ReceiveEntry
        <3>3. RetainedShape'
            BY SMT, <1>12 DEF DurableData, RetainedShape, ReceiveEntry
        <3> QED BY <3>1, <3>2, <3>3
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>12 DEF ReceiveEntry, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>12 DEF ReceiveEntry, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>12, <2>2 DEF ReceiveEntry, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>13. \A r \in Replicas : \A o : AckEntry(r, o) => DurabilityStep
    BY SMT DEF AckEntry, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>14. ASSUME NEW r \in Replicas, NEW source, NEW p, NEW e, CopyProposalEntry(r, source, p, e)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        BY SMT, <1>14 DEF DurableData, StorageShape, FormalShape, RetainedShape, CopyProposalEntry
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>14 DEF CopyProposalEntry, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>14 DEF CopyProposalEntry, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>14, <2>2 DEF CopyProposalEntry, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>15. ASSUME NEW r \in Replicas, NEW p, RetainProposal(r, p)
        PROVE DurabilityStep
    <2>1. StorageShape' /\ FormalShape' /\ RetainedShape'
        BY SMT, <1>15 DEF DurableData, StorageShape, FormalShape, RetainedShape, RetainProposal
    <2>2. ackMessages \subseteq ackMessages'
          /\ (\A storedReplica \in Replicas : stored[storedReplica] \subseteq stored'[storedReplica])
          /\ (\A a \in ackMessages' \ ackMessages :
                    a.sender \in Replicas /\ a.contents \subseteq stored'[a.sender])
        BY SMT, <1>15 DEF RetainProposal, DurableData, StorageShape
    <2>3. FormalStored'
        BY SMT, <1>15 DEF RetainProposal, DurableData, FormalStored, StorageShape, FormalShape
    <2>4. RetainedStored'
        BY SMT, <1>15, <2>2 DEF RetainProposal, DurableData, RetainedStored, RetainedShape, StorageShape
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep, DurableData
<1>16. \A r \in Replicas : \A p : AckProposal(r, p) => DurabilityStep
    BY SMT DEF AckProposal, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>17. \A c \in Replicas : \A m : DeliverAck(c, m) => DurabilityStep
    BY SMT DEF DeliverAck, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>18. \A c \in Replicas : ConfirmProposal(c) => DurabilityStep
    BY SMT DEF ConfirmProposal, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>19. \A r \in Replicas : \A p : LearnConfirmation(r, p) => DurabilityStep
    BY SMT DEF LearnConfirmation, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>20. \A c \in Replicas : \A e : CommitEntry(c, e) => DurabilityStep
    BY SMT DEF CommitEntry, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>21. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => DurabilityStep
    BY SMT DEF AdvertiseCommit, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>22. \A r \in Replicas : \A m : LearnCommit(r, m) => DurabilityStep
    BY SMT DEF LearnCommit, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>23. \A c \in Replicas : Activate(c) => DurabilityStep
    BY SMT DEF Activate, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>24. \A r \in Replicas : \A e : ApplyEntry(r, e) => DurabilityStep
    BY SMT DEF ApplyEntry, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>25. \A r \in Replicas : Crash(r) => DurabilityStep
    BY SMT DEF Crash, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1>26. \A r \in Replicas : Restart(r) => DurabilityStep
    BY SMT DEF Restart, DurabilityStep, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, Ack, Publish
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
    DEF ProtocolNext, AdministrativeNext

THEOREM DurabilityInitially == Init => DurabilityInvariant
BY SMT DEF Init, DurabilityInvariant, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, AckSendersValid, AckDurability

THEOREM DurabilityInductiveStep ==
    ASSUME DurabilityInvariant, Next
    PROVE DurabilityInvariant'
<1>1. DurabilityStep
    BY EveryStepPreservesDurabilityFacts DEF DurabilityInvariant, Next
<1>2. \A a \in ackMessages : a.contents \subseteq stored'[a.sender]
    BY SMT, <1>1 DEF DurabilityInvariant, DurabilityStep, AckSendersValid, AckDurability
<1> QED BY SMT, <1>1, <1>2
    DEF DurabilityInvariant, DurabilityStep, AckSendersValid, AckDurability

THEOREM DurabilityStuttering ==
    ASSUME DurabilityInvariant, UNCHANGED vars
    PROVE DurabilityInvariant'
BY SMT DEF DurabilityInvariant, DurableData, StorageShape, FormalShape, RetainedShape, FormalStored, RetainedStored, AckSendersValid, AckDurability,
           vars, protocolVars, observerVars

THEOREM ProtocolAckDurability == Spec => []DurabilityInvariant
<1>1. Init => DurabilityInvariant
    BY DurabilityInitially
<1>2. DurabilityInvariant /\ [Next]_vars => DurabilityInvariant'
    BY DurabilityInductiveStep, DurabilityStuttering
<1> QED BY PTL, <1>1, <1>2 DEF Spec

THEOREM EvidenceInitially == Init => CommitEvidenceSound
BY SMT DEF Init, CommitEvidenceSound, Evidence

THEOREM EvidenceInductiveStep ==
    ASSUME DurabilityInvariant, CommitEvidenceSound, Next
    PROVE CommitEvidenceSound'
<1>1. ackMessages \subseteq ackMessages' /\ Observe
    BY SMT, EveryStepPreservesDurabilityFacts DEF Next, DurabilityInvariant, DurabilityStep
<1> QED BY ObserverPreservesIndependentEvidence, <1>1

THEOREM EvidenceStuttering ==
    ASSUME CommitEvidenceSound, UNCHANGED vars
    PROVE CommitEvidenceSound'
BY SMT DEF CommitEvidenceSound, vars, protocolVars, observerVars

THEOREM ProtocolIndependentEvidence == Spec => []CommitEvidenceSound
<1>1. Spec => []DurabilityInvariant
    BY ProtocolAckDurability
<1>2. Init => CommitEvidenceSound
    BY EvidenceInitially
<1>3. DurabilityInvariant /\ CommitEvidenceSound /\ [Next]_vars => CommitEvidenceSound'
    BY EvidenceInductiveStep, EvidenceStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
