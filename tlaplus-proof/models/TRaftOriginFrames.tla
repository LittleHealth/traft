-------------------------- MODULE TRaftOriginFrames -------------------------
EXTENDS TRaftOriginSupport

FormalAnchorChanges ==
    \/ \E r \in Replicas : \E v : CreateEntry(r, v)
    \/ \E r \in Replicas : \E v, k : CreateSuccessor(r, v, k)
    \/ \E r \in Replicas : \E o : ReceiveEntry(r, o)
    \/ \E r \in Replicas : ConfirmProposal(r)
    \/ \E r \in Replicas : \E p : LearnConfirmation(r, p)

THEOREM FormalAnchorActionProjection ==
    ASSUME TypeOK, ProtocolNext
    PROVE FormalAnchorChanges \/
          (UNCHANGED formal /\ \A r \in Replicas : retained[r] \subseteq retained'[r])
<1>1. \A c : StartElection(c) => UNCHANGED <<formal, retained>>
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED <<formal, retained>>
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED <<formal, retained>>
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED <<formal, retained>>
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED <<formal, retained>>
    BY SMT DEF WinElection
<1>6. \A r, req : MakeReport(r, req) => UNCHANGED <<formal, retained>>
    BY SMT DEF MakeReport
<1>7. \A c, m : DeliverReport(c, m) => UNCHANGED <<formal, retained>>
    BY SMT DEF DeliverReport
<1>8. \A c, p : BuildRecovery(c, p) => UNCHANGED <<formal, retained>>
    BY SMT DEF BuildRecovery
<1>9. \A c, e : SendEntry(c, e) => UNCHANGED <<formal, retained>>
    BY SMT DEF SendEntry
<1>10. \A r, o : AckEntry(r, o) => UNCHANGED <<formal, retained>>
    BY SMT DEF AckEntry
<1>11. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED <<formal, retained>>
    BY SMT DEF CopyProposalEntry
<1>12. \A r \in Replicas : \A p : RetainProposal(r, p) =>
          (UNCHANGED formal /\ \A s \in Replicas : retained[s] \subseteq retained'[s])
    BY SMT DEF RetainProposal, TypeOK
<1>13. \A r, p : AckProposal(r, p) => UNCHANGED <<formal, retained>>
    BY SMT DEF AckProposal
<1>14. \A c, m : DeliverAck(c, m) => UNCHANGED <<formal, retained>>
    BY SMT DEF DeliverAck
<1>15. \A c, e : CommitEntry(c, e) => UNCHANGED <<formal, retained>>
    BY SMT DEF CommitEntry
<1>16. \A c, e : AdvertiseCommit(c, e) => UNCHANGED <<formal, retained>>
    BY SMT DEF AdvertiseCommit
<1>17. \A r, m : LearnCommit(r, m) => UNCHANGED <<formal, retained>>
    BY SMT DEF LearnCommit
<1>18. \A c : Activate(c) => UNCHANGED <<formal, retained>>
    BY SMT DEF Activate
<1>19. \A r, e : ApplyEntry(r, e) => UNCHANGED <<formal, retained>>
    BY SMT DEF ApplyEntry
<1>20. \A r : Crash(r) => UNCHANGED <<formal, retained>>
    BY SMT DEF Crash
<1>21. \A r : Restart(r) => UNCHANGED <<formal, retained>>
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
    DEF ProtocolNext, AdministrativeNext, FormalAnchorChanges

THEOREM ReportAnchorActionProjection ==
    ProtocolNext => (\E r \in Replicas : \E req : MakeReport(r, req)) \/ UNCHANGED reportMessages
<1>1. \A c : StartElection(c) => UNCHANGED reportMessages
    BY SMT DEF StartElection
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED reportMessages
    BY SMT DEF AdoptTerm
<1>3. \A r, req : GrantVote(r, req) => UNCHANGED reportMessages
    BY SMT DEF GrantVote
<1>4. \A c, m : DeliverVote(c, m) => UNCHANGED reportMessages
    BY SMT DEF DeliverVote
<1>5. \A c : WinElection(c) => UNCHANGED reportMessages
    BY SMT DEF WinElection
<1>6. \A c, m : DeliverReport(c, m) => UNCHANGED reportMessages
    BY SMT DEF DeliverReport
<1>7. \A c, p : BuildRecovery(c, p) => UNCHANGED reportMessages
    BY SMT DEF BuildRecovery
<1>8. \A c, v : CreateEntry(c, v) => UNCHANGED reportMessages
    BY SMT DEF CreateEntry
<1>9. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED reportMessages
    BY SMT DEF CreateSuccessor
<1>10. \A c, e : SendEntry(c, e) => UNCHANGED reportMessages
    BY SMT DEF SendEntry
<1>11. \A r, o : ReceiveEntry(r, o) => UNCHANGED reportMessages
    BY SMT DEF ReceiveEntry
<1>12. \A r, o : AckEntry(r, o) => UNCHANGED reportMessages
    BY SMT DEF AckEntry
<1>13. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED reportMessages
    BY SMT DEF CopyProposalEntry
<1>14. \A r, p : RetainProposal(r, p) => UNCHANGED reportMessages
    BY SMT DEF RetainProposal
<1>15. \A r, p : AckProposal(r, p) => UNCHANGED reportMessages
    BY SMT DEF AckProposal
<1>16. \A c, m : DeliverAck(c, m) => UNCHANGED reportMessages
    BY SMT DEF DeliverAck
<1>17. \A c : ConfirmProposal(c) => UNCHANGED reportMessages
    BY SMT DEF ConfirmProposal
<1>18. \A r, p : LearnConfirmation(r, p) => UNCHANGED reportMessages
    BY SMT DEF LearnConfirmation
<1>19. \A c, e : CommitEntry(c, e) => UNCHANGED reportMessages
    BY SMT DEF CommitEntry
<1>20. \A c, e : AdvertiseCommit(c, e) => UNCHANGED reportMessages
    BY SMT DEF AdvertiseCommit
<1>21. \A r, m : LearnCommit(r, m) => UNCHANGED reportMessages
    BY SMT DEF LearnCommit
<1>22. \A c : Activate(c) => UNCHANGED reportMessages
    BY SMT DEF Activate
<1>23. \A r, e : ApplyEntry(r, e) => UNCHANGED reportMessages
    BY SMT DEF ApplyEntry
<1>24. \A r : Crash(r) => UNCHANGED reportMessages
    BY SMT DEF Crash
<1>25. \A r : Restart(r) => UNCHANGED reportMessages
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25
    DEF ProtocolNext, AdministrativeNext
=============================================================================
