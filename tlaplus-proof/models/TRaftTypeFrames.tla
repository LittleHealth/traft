-------------------------- MODULE TRaftTypeFrames ---------------------------
EXTENDS TRaftCore, TLAPS

LogTypeVars == <<formal, stored, knownCommitted, applied, retained, proposals>>
LogTypeChanges ==
    \/ \E c \in Replicas : \E p : BuildRecovery(c, p)
    \/ \E c \in Replicas : \E v : CreateEntry(c, v)
    \/ \E c \in Replicas : \E v, k : CreateSuccessor(c, v, k)
    \/ \E r \in Replicas : \E o : ReceiveEntry(r, o)
    \/ \E r, s \in Replicas : \E p, e : CopyProposalEntry(r, s, p, e)
    \/ \E r \in Replicas : \E p : RetainProposal(r, p)
    \/ \E c \in Replicas : ConfirmProposal(c)
    \/ \E r \in Replicas : \E p : LearnConfirmation(r, p)
    \/ \E c \in Replicas : \E e : CommitEntry(c, e)
    \/ \E r \in Replicas : \E m : LearnCommit(r, m)
    \/ \E r \in Replicas : \E e : ApplyEntry(r, e)

THEOREM LogTypeActionProjection == ProtocolNext => LogTypeChanges \/ UNCHANGED LogTypeVars
<1>1. \A c : StartElection(c) => UNCHANGED LogTypeVars
    BY SMT DEF StartElection, LogTypeVars
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED LogTypeVars
    BY SMT DEF AdoptTerm, LogTypeVars
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED LogTypeVars
    BY SMT DEF GrantVote, LogTypeVars
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED LogTypeVars
    BY SMT DEF DeliverVote, LogTypeVars
<1>5. \A c : WinElection(c) => UNCHANGED LogTypeVars
    BY SMT DEF WinElection, LogTypeVars
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED LogTypeVars
    BY SMT DEF MakeReport, LogTypeVars
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED LogTypeVars
    BY SMT DEF DeliverReport, LogTypeVars
<1>8. \A c, e : SendEntry(c, e) => UNCHANGED LogTypeVars
    BY SMT DEF SendEntry, LogTypeVars
<1>9. \A r, o : AckEntry(r, o) => UNCHANGED LogTypeVars
    BY SMT DEF AckEntry, LogTypeVars
<1>10. \A r, p : AckProposal(r, p) => UNCHANGED LogTypeVars
    BY SMT DEF AckProposal, LogTypeVars
<1>11. \A c, m : DeliverAck(c, m) => UNCHANGED LogTypeVars
    BY SMT DEF DeliverAck, LogTypeVars
<1>12. \A c, e : AdvertiseCommit(c, e) => UNCHANGED LogTypeVars
    BY SMT DEF AdvertiseCommit, LogTypeVars
<1>13. \A c : Activate(c) => UNCHANGED LogTypeVars
    BY SMT DEF Activate, LogTypeVars
<1>14. \A r : Crash(r) => UNCHANGED LogTypeVars
    BY SMT DEF Crash, LogTypeVars
<1>15. \A r : Restart(r) => UNCHANGED LogTypeVars
    BY SMT DEF Restart, LogTypeVars
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15 DEF ProtocolNext, AdministrativeNext, LogTypeChanges

THEOREM AliveActionProjection ==
    ProtocolNext => (\E r \in Replicas : Crash(r) \/ Restart(r)) \/ UNCHANGED alive
<1>1. \A c : StartElection(c) => UNCHANGED alive
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED alive
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED alive
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED alive
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED alive
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED alive
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED alive
    BY SMT DEF DeliverReport
<1>8. \A c, p : BuildRecovery(c, p) => UNCHANGED alive
    BY SMT DEF BuildRecovery
<1>9. \A c, v : CreateEntry(c, v) => UNCHANGED alive
    BY SMT DEF CreateEntry
<1>10. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED alive
    BY SMT DEF CreateSuccessor
<1>11. \A c, e : SendEntry(c, e) => UNCHANGED alive
    BY SMT DEF SendEntry
<1>12. \A r, o : ReceiveEntry(r, o) => UNCHANGED alive
    BY SMT DEF ReceiveEntry
<1>13. \A r, o : AckEntry(r, o) => UNCHANGED alive
    BY SMT DEF AckEntry
<1>14. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED alive
    BY SMT DEF CopyProposalEntry
<1>15. \A r, p : RetainProposal(r, p) => UNCHANGED alive
    BY SMT DEF RetainProposal
<1>16. \A r, p : AckProposal(r, p) => UNCHANGED alive
    BY SMT DEF AckProposal
<1>17. \A c, m : DeliverAck(c, m) => UNCHANGED alive
    BY SMT DEF DeliverAck
<1>18. \A c : ConfirmProposal(c) => UNCHANGED alive
    BY SMT DEF ConfirmProposal
<1>19. \A r, p : LearnConfirmation(r, p) => UNCHANGED alive
    BY SMT DEF LearnConfirmation
<1>20. \A c, e : CommitEntry(c, e) => UNCHANGED alive
    BY SMT DEF CommitEntry
<1>21. \A c, e : AdvertiseCommit(c, e) => UNCHANGED alive
    BY SMT DEF AdvertiseCommit
<1>22. \A r, m : LearnCommit(r, m) => UNCHANGED alive
    BY SMT DEF LearnCommit
<1>23. \A c : Activate(c) => UNCHANGED alive
    BY SMT DEF Activate
<1>24. \A r, e : ApplyEntry(r, e) => UNCHANGED alive
    BY SMT DEF ApplyEntry
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24 DEF ProtocolNext, AdministrativeNext
=============================================================================
