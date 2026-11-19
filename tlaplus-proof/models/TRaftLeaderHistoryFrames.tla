----------------------- MODULE TRaftLeaderHistoryFrames ---------------------
EXTENDS TRaftLeaderHistoryState, TRaftElectionState, TLAPS

LeaderControlChanges ==
    \/ \E r \in Replicas : StartElection(r) \/ WinElection(r) \/ Activate(r) \/ Crash(r)
    \/ \E r \in Replicas : \E t : AdoptTerm(r, t)

THEOREM LeaderControlProjection ==
    ProtocolNext => LeaderControlChanges \/ UNCHANGED <<term, role>>
<1>1. \A r, req : GrantVote(r, req) => UNCHANGED <<term, role>>
    BY SMT DEF GrantVote
<1>2. \A c, m : DeliverVote(c, m) => UNCHANGED <<term, role>>
    BY SMT DEF DeliverVote
<1>3. \A r, req : MakeReport(r, req) => UNCHANGED <<term, role>>
    BY SMT DEF MakeReport
<1>4. \A c, m : DeliverReport(c, m) => UNCHANGED <<term, role>>
    BY SMT DEF DeliverReport
<1>5. \A c, p : BuildRecovery(c, p) => UNCHANGED <<term, role>>
    BY SMT DEF BuildRecovery
<1>6. \A c, v : CreateEntry(c, v) => UNCHANGED <<term, role>>
    BY SMT DEF CreateEntry
<1>7. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED <<term, role>>
    BY SMT DEF CreateSuccessor
<1>8. \A c, e : SendEntry(c, e) => UNCHANGED <<term, role>>
    BY SMT DEF SendEntry
<1>9. \A r, o : ReceiveEntry(r, o) => UNCHANGED <<term, role>>
    BY SMT DEF ReceiveEntry
<1>10. \A r, o : AckEntry(r, o) => UNCHANGED <<term, role>>
    BY SMT DEF AckEntry
<1>11. \A r, s, p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED <<term, role>>
    BY SMT DEF CopyProposalEntry
<1>12. \A r, p : RetainProposal(r, p) => UNCHANGED <<term, role>>
    BY SMT DEF RetainProposal
<1>13. \A r, p : AckProposal(r, p) => UNCHANGED <<term, role>>
    BY SMT DEF AckProposal
<1>14. \A c, m : DeliverAck(c, m) => UNCHANGED <<term, role>>
    BY SMT DEF DeliverAck
<1>15. \A c : ConfirmProposal(c) => UNCHANGED <<term, role>>
    BY SMT DEF ConfirmProposal
<1>16. \A r, p : LearnConfirmation(r, p) => UNCHANGED <<term, role>>
    BY SMT DEF LearnConfirmation
<1>17. \A c, e : CommitEntry(c, e) => UNCHANGED <<term, role>>
    BY SMT DEF CommitEntry
<1>18. \A c, e : AdvertiseCommit(c, e) => UNCHANGED <<term, role>>
    BY SMT DEF AdvertiseCommit
<1>19. \A r, m : LearnCommit(r, m) => UNCHANGED <<term, role>>
    BY SMT DEF LearnCommit
<1>20. \A r, e : ApplyEntry(r, e) => UNCHANGED <<term, role>>
    BY SMT DEF ApplyEntry
<1>21. \A r : Restart(r) => UNCHANGED <<term, role>>
    BY SMT DEF Restart
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
    DEF ProtocolNext, AdministrativeNext, LeaderControlChanges
=============================================================================
