---------------------- MODULE TRaftApplicationOrderProof ---------------------
EXTENDS TRaftCore, TRaftFunctionProof

AppliedShape == applied = [r \in Replicas |-> applied[r]]
OrderInvariant == AppliedShape /\ ApplicationOrder
OrderCheck == \A r \in Replicas :
                    /\ applied[r] \subseteq applied'[r]
                    /\ \A e \in applied'[r] \ applied[r] :
                         /\ e \in formal[r] \cap knownCommitted[r]
                         /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]

OrderFacts == AppliedShape' /\ OrderCheck

THEOREM OnlyApplyChangesApplied ==
    ProtocolNext => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
<1>1. \A c \in Replicas : StartElection(c) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF StartElection
<1>2. \A r \in Replicas : \A t : AdoptTerm(r, t) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF AdoptTerm
<1>3. \A r \in Replicas : \A req : GrantVote(r, req) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF GrantVote
<1>4. \A c \in Replicas : \A m : DeliverVote(c, m) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF DeliverVote
<1>5. \A c \in Replicas : WinElection(c) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF WinElection
<1>6. \A r \in Replicas : \A req : MakeReport(r, req) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF MakeReport
<1>7. \A c \in Replicas : \A m : DeliverReport(c, m) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF DeliverReport
<1>8. \A c \in Replicas : \A p : BuildRecovery(c, p) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF BuildRecovery
<1>9. \A c \in Replicas : \A v : CreateEntry(c, v) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF CreateEntry
<1>10. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF CreateSuccessor
<1>11. \A c \in Replicas : \A e : SendEntry(c, e) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF SendEntry
<1>12. \A r \in Replicas : \A o : ReceiveEntry(r, o) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF ReceiveEntry
<1>13. \A r \in Replicas : \A o : AckEntry(r, o) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF AckEntry
<1>14. \A r, s \in Replicas : \A p, e : CopyProposalEntry(r, s, p, e) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF CopyProposalEntry
<1>15. \A r \in Replicas : \A p : RetainProposal(r, p) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF RetainProposal
<1>16. \A r \in Replicas : \A p : AckProposal(r, p) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF AckProposal
<1>17. \A c \in Replicas : \A m : DeliverAck(c, m) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF DeliverAck
<1>18. \A c \in Replicas : ConfirmProposal(c) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF ConfirmProposal
<1>19. \A r \in Replicas : \A p : LearnConfirmation(r, p) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF LearnConfirmation
<1>20. \A c \in Replicas : \A e : CommitEntry(c, e) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF CommitEntry
<1>21. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF AdvertiseCommit
<1>22. \A r \in Replicas : \A m : LearnCommit(r, m) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF LearnCommit
<1>23. \A c \in Replicas : Activate(c) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF Activate
<1>24. \A r \in Replicas : \A e : ApplyEntry(r, e) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT
<1>25. \A r \in Replicas : Crash(r) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF Crash
<1>26. \A r \in Replicas : Restart(r) => ((\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied)
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
    DEF ProtocolNext, AdministrativeNext

THEOREM ApplyEntryEstablishesOrderFacts ==
    ASSUME AppliedShape, NEW r \in Replicas, NEW e, ApplyEntry(r, e)
    PROVE OrderFacts
<1>1. AppliedShape'
    BY SMT, FunctionUpdatePreservesDomainShape DEF AppliedShape, ApplyEntry
<1>2. \A s \in Replicas :
          /\ applied[s] \subseteq applied'[s]
          /\ \A x \in applied'[s] \ applied[s] :
               /\ x \in formal[s] \cap knownCommitted[s]
               /\ Prefix(formal[s], x.part - 1) \subseteq applied[s]
    <2>1. SUFFICES ASSUME NEW s \in Replicas
                  PROVE /\ applied[s] \subseteq applied'[s]
                        /\ \A x \in applied'[s] \ applied[s] :
                             /\ x \in formal[s] \cap knownCommitted[s]
                             /\ Prefix(formal[s], x.part - 1) \subseteq applied[s]
        OBVIOUS
    <2>2. applied' = [applied EXCEPT ![r] = applied[r] \cup {e}]
          /\ e \in (formal[r] \cap knownCommitted[r]) \ applied[r]
          /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]
        BY DEF ApplyEntry
    <2>3. CASE s = r
        <3>1. applied'[s] = applied[s] \cup {e}
            BY SMT, <2>1, <2>2, <2>3 DEF AppliedShape
        <3>2. applied'[s] \ applied[s] = {e}
            BY ONLY SMT, <2>2, <2>3, <3>1
        <3> QED BY ONLY SMT, <2>2, <2>3, <3>1, <3>2
    <2>4. CASE s # r
        <3>1. applied'[s] = applied[s]
            BY SMT, <2>1, <2>2, <2>4 DEF AppliedShape
        <3> QED BY ONLY SMT, <3>1
    <2> QED BY <2>3, <2>4
<1> QED BY <1>1, <1>2 DEF OrderFacts, OrderCheck

THEOREM OrderInitially == Init => OrderInvariant
BY SMT DEF Init, OrderInvariant, AppliedShape, ApplicationOrder

THEOREM OrderInductiveStep ==
    ASSUME OrderInvariant, Next
    PROVE OrderInvariant'
<1>1. (\E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)) \/ UNCHANGED applied
    BY OnlyApplyChangesApplied DEF Next
<1>2. OrderFacts
    <2>1. AppliedShape
        BY DEF OrderInvariant
    <2>2. CASE UNCHANGED applied
        BY ONLY SMT, <2>1, <2>2 DEF OrderFacts, OrderCheck, AppliedShape
    <2>3. CASE \E applyNode \in Replicas : \E applyItem : ApplyEntry(applyNode, applyItem)
        BY ONLY SMT, <2>1, <2>3, ApplyEntryEstablishesOrderFacts
    <2> QED BY <1>1, <2>2, <2>3
<1>3. applicationOrderOK
    BY DEF OrderInvariant, ApplicationOrder
<1>4. applicationOrderOK' = (applicationOrderOK /\ OrderCheck)
    BY DEF Next, Observe, OrderCheck
<1>5. AppliedShape' /\ OrderCheck
    BY <1>2 DEF OrderFacts
<1>6. applicationOrderOK'
    BY ONLY ZenonT(5), <1>3, <1>4, <1>5
<1> QED BY ONLY ZenonT(5), <1>5, <1>6
    DEF OrderInvariant, ApplicationOrder

THEOREM OrderStuttering ==
    ASSUME OrderInvariant, UNCHANGED vars
    PROVE OrderInvariant'
BY SMT DEF OrderInvariant, AppliedShape, ApplicationOrder, vars, protocolVars, observerVars

THEOREM ProtocolApplicationOrder == Spec => []OrderInvariant
<1>1. Init => OrderInvariant
    BY OrderInitially
<1>2. OrderInvariant /\ [Next]_vars => OrderInvariant'
    BY OrderInductiveStep, OrderStuttering
<1> QED BY PTL, <1>1, <1>2 DEF Spec
=============================================================================
