---------------------- MODULE TRaftBoundaryCountFrames ----------------------
EXTENDS TRaftBoundaryCountSupport

BoundaryCountChanges ==
    \/ \E c \in Replicas : \E p : BuildRecovery(c, p)
    \/ \E c \in Replicas : \E v : CreateEntry(c, v)
    \/ \E c \in Replicas : \E v, k : CreateSuccessor(c, v, k)
    \/ \E r \in Replicas : \E o : ReceiveEntry(r, o)
    \/ \E c \in Replicas : ConfirmProposal(c)
    \/ \E r \in Replicas : \E p : LearnConfirmation(r, p)

THEOREM BoundaryCountActionProjection ==
    ProtocolNext => BoundaryCountChanges \/ UNCHANGED <<formal, proposals>>
<1>1. \A c : StartElection(c) => UNCHANGED <<formal, proposals>>
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED <<formal, proposals>>
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED <<formal, proposals>>
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED <<formal, proposals>>
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED <<formal, proposals>>
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED <<formal, proposals>>
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED <<formal, proposals>>
    BY SMT DEF DeliverReport
<1>8. \A c, e : SendEntry(c, e) => UNCHANGED <<formal, proposals>>
    BY SMT DEF SendEntry
<1>9. \A r, o : AckEntry(r, o) => UNCHANGED <<formal, proposals>>
    BY SMT DEF AckEntry
<1>10. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED <<formal, proposals>>
    BY SMT DEF CopyProposalEntry
<1>11. \A r, p : RetainProposal(r, p) => UNCHANGED <<formal, proposals>>
    BY SMT DEF RetainProposal
<1>12. \A r, p : AckProposal(r, p) => UNCHANGED <<formal, proposals>>
    BY SMT DEF AckProposal
<1>13. \A c, m : DeliverAck(c, m) => UNCHANGED <<formal, proposals>>
    BY SMT DEF DeliverAck
<1>14. \A c, e : CommitEntry(c, e) => UNCHANGED <<formal, proposals>>
    BY SMT DEF CommitEntry
<1>15. \A c, e : AdvertiseCommit(c, e) => UNCHANGED <<formal, proposals>>
    BY SMT DEF AdvertiseCommit
<1>16. \A r, m : LearnCommit(r, m) => UNCHANGED <<formal, proposals>>
    BY SMT DEF LearnCommit
<1>17. \A c : Activate(c) => UNCHANGED <<formal, proposals>>
    BY SMT DEF Activate
<1>18. \A r, e : ApplyEntry(r, e) => UNCHANGED <<formal, proposals>>
    BY SMT DEF ApplyEntry
<1>19. \A r : Crash(r) => UNCHANGED <<formal, proposals>>
    BY SMT DEF Crash
<1>20. \A r : Restart(r) => UNCHANGED <<formal, proposals>>
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20
    DEF ProtocolNext, AdministrativeNext, BoundaryCountChanges
=============================================================================
