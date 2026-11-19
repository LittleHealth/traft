------------------------- MODULE TRaftRetainedFrames -------------------------
EXTENDS TRaftCore, TLAPS

THEOREM OnlyRetainChangesRetained ==
    ProtocolNext => (\E r \in Replicas : \E p : RetainProposal(r, p)) \/ UNCHANGED retained
<1>1. \A c : StartElection(c) => UNCHANGED retained
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED retained
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED retained
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED retained
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED retained
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED retained
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED retained
    BY SMT DEF DeliverReport
<1>8. \A c, p : BuildRecovery(c, p) => UNCHANGED retained
    BY SMT DEF BuildRecovery
<1>9. \A c, v : CreateEntry(c, v) => UNCHANGED retained
    BY SMT DEF CreateEntry
<1>10. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED retained
    BY SMT DEF CreateSuccessor
<1>11. \A c, e : SendEntry(c, e) => UNCHANGED retained
    BY SMT DEF SendEntry
<1>12. \A r, o : ReceiveEntry(r, o) => UNCHANGED retained
    BY SMT DEF ReceiveEntry
<1>13. \A r, o : AckEntry(r, o) => UNCHANGED retained
    BY SMT DEF AckEntry
<1>14. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED retained
    BY SMT DEF CopyProposalEntry
<1>15. \A r, p : AckProposal(r, p) => UNCHANGED retained
    BY SMT DEF AckProposal
<1>16. \A c, m : DeliverAck(c, m) => UNCHANGED retained
    BY SMT DEF DeliverAck
<1>17. \A c : ConfirmProposal(c) => UNCHANGED retained
    BY SMT DEF ConfirmProposal
<1>18. \A r, p : LearnConfirmation(r, p) => UNCHANGED retained
    BY SMT DEF LearnConfirmation
<1>19. \A c, e : CommitEntry(c, e) => UNCHANGED retained
    BY SMT DEF CommitEntry
<1>20. \A c, e : AdvertiseCommit(c, e) => UNCHANGED retained
    BY SMT DEF AdvertiseCommit
<1>21. \A r, m : LearnCommit(r, m) => UNCHANGED retained
    BY SMT DEF LearnCommit
<1>22. \A c : Activate(c) => UNCHANGED retained
    BY SMT DEF Activate
<1>23. \A r, e : ApplyEntry(r, e) => UNCHANGED retained
    BY SMT DEF ApplyEntry
<1>24. \A r : Crash(r) => UNCHANGED retained
    BY SMT DEF Crash
<1>25. \A r : Restart(r) => UNCHANGED retained
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25
    DEF ProtocolNext, AdministrativeNext

THEOREM RetainedChangeHasCurrentEpoch ==
    ASSUME retained = [r \in Replicas |-> retained[r]], ProtocolNext
    PROVE /\ \A r \in Replicas : retained[r] \subseteq retained'[r]
          /\ \A r \in Replicas : \A p \in retained'[r] \ retained[r] : p.epoch = term[r]
<1>1. (\E r \in Replicas : \E p : RetainProposal(r, p)) \/ UNCHANGED retained
    BY OnlyRetainChangesRetained
<1>2. ASSUME NEW r \in Replicas, NEW p, RetainProposal(r, p)
      PROVE /\ \A s \in Replicas : retained[s] \subseteq retained'[s]
            /\ \A s \in Replicas : \A q \in retained'[s] \ retained[s] : q.epoch = term[s]
    BY SMT, <1>2 DEF RetainProposal
<1> QED BY SMT, <1>1, <1>2
=============================================================================
