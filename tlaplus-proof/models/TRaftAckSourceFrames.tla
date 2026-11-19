------------------------ MODULE TRaftAckSourceFrames -------------------------
EXTENDS TRaftCore, TLAPS

THEOREM OnlyAckActionsChangeMessages ==
    ProtocolNext => (\E r \in Replicas : \E o : AckEntry(r, o))
                  \/ (\E r \in Replicas : \E p : AckProposal(r, p))
                  \/ UNCHANGED ackMessages
<1>1. \A c : StartElection(c) => UNCHANGED ackMessages
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED ackMessages
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED ackMessages
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED ackMessages
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED ackMessages
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED ackMessages
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED ackMessages
    BY SMT DEF DeliverReport
<1>8. \A c, p : BuildRecovery(c, p) => UNCHANGED ackMessages
    BY SMT DEF BuildRecovery
<1>9. \A c, v : CreateEntry(c, v) => UNCHANGED ackMessages
    BY SMT DEF CreateEntry
<1>10. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED ackMessages
    BY SMT DEF CreateSuccessor
<1>11. \A c, e : SendEntry(c, e) => UNCHANGED ackMessages
    BY SMT DEF SendEntry
<1>12. \A r, o : ReceiveEntry(r, o) => UNCHANGED ackMessages
    BY SMT DEF ReceiveEntry
<1>13. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED ackMessages
    BY SMT DEF CopyProposalEntry
<1>14. \A r, p : RetainProposal(r, p) => UNCHANGED ackMessages
    BY SMT DEF RetainProposal
<1>15. \A c, m : DeliverAck(c, m) => UNCHANGED ackMessages
    BY SMT DEF DeliverAck
<1>16. \A c : ConfirmProposal(c) => UNCHANGED ackMessages
    BY SMT DEF ConfirmProposal
<1>17. \A r, p : LearnConfirmation(r, p) => UNCHANGED ackMessages
    BY SMT DEF LearnConfirmation
<1>18. \A c, e : CommitEntry(c, e) => UNCHANGED ackMessages
    BY SMT DEF CommitEntry
<1>19. \A c, e : AdvertiseCommit(c, e) => UNCHANGED ackMessages
    BY SMT DEF AdvertiseCommit
<1>20. \A r, m : LearnCommit(r, m) => UNCHANGED ackMessages
    BY SMT DEF LearnCommit
<1>21. \A c : Activate(c) => UNCHANGED ackMessages
    BY SMT DEF Activate
<1>22. \A r, e : ApplyEntry(r, e) => UNCHANGED ackMessages
    BY SMT DEF ApplyEntry
<1>23. \A r : Crash(r) => UNCHANGED ackMessages
    BY SMT DEF Crash
<1>24. \A r : Restart(r) => UNCHANGED ackMessages
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24
    DEF ProtocolNext, AdministrativeNext
=============================================================================
