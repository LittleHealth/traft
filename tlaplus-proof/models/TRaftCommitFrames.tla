-------------------------- MODULE TRaftCommitFrames --------------------------
EXTENDS TRaftCommitSupport

THEOREM EveryStepPreservesInboxOrigins ==
    ASSUME AckInboxOrigins, ackMessages \subseteq ackMessages', ProtocolNext
    PROVE AckInboxOrigins'
<1>0. AckInboxOrigins /\ ackMessages \subseteq ackMessages' /\ ProtocolNext
    OBVIOUS
<1>1. ASSUME NEW c \in Replicas, StartElection(c)
      PROVE AckInboxOrigins'
    <2>1. c \in Replicas /\ ackInbox' = [ackInbox EXCEPT ![c] = {}]
        BY <1>1 DEF StartElection
    <2> QED BY ONLY InboxResetOrigins, <1>0, <2>1
<1>2. ASSUME NEW r \in Replicas, NEW t, AdoptTerm(r, t)
      PROVE AckInboxOrigins'
    <2>1. r \in Replicas /\ ackInbox' = [ackInbox EXCEPT ![r] = {}]
        BY <1>2 DEF AdoptTerm
    <2> QED BY ONLY InboxResetOrigins, <1>0, <2>1
<1>3. \A r \in Replicas : \A req : GrantVote(r, req) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF GrantVote
<1>4. \A c \in Replicas : \A m : DeliverVote(c, m) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF DeliverVote
<1>5. \A c \in Replicas : WinElection(c) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF WinElection
<1>6. \A r \in Replicas : \A req : MakeReport(r, req) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF MakeReport
<1>7. \A c \in Replicas : \A m : DeliverReport(c, m) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF DeliverReport
<1>8. \A c \in Replicas : \A p : BuildRecovery(c, p) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF BuildRecovery
<1>9. \A c \in Replicas : \A v : CreateEntry(c, v) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF CreateEntry
<1>10. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF CreateSuccessor
<1>11. \A c \in Replicas : \A e : SendEntry(c, e) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF SendEntry
<1>12. \A r \in Replicas : \A o : ReceiveEntry(r, o) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF ReceiveEntry
<1>13. \A r \in Replicas : \A o : AckEntry(r, o) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF AckEntry
<1>14. \A r, s \in Replicas : \A p, e : CopyProposalEntry(r, s, p, e) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF CopyProposalEntry
<1>15. \A r \in Replicas : \A p : RetainProposal(r, p) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF RetainProposal
<1>16. \A r \in Replicas : \A p : AckProposal(r, p) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF AckProposal
<1>17. ASSUME NEW c \in Replicas, NEW m, DeliverAck(c, m)
      PROVE AckInboxOrigins'
    <2>1. c \in Replicas /\ ackInbox' = [ackInbox EXCEPT ![c] = @ \cup {m}] /\ m \in ackMessages
        BY <1>17 DEF DeliverAck
    <2> QED BY ONLY InboxReceiveOrigins, <1>0, <2>1
<1>18. \A c \in Replicas : ConfirmProposal(c) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF ConfirmProposal
<1>19. \A r \in Replicas : \A p : LearnConfirmation(r, p) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF LearnConfirmation
<1>20. \A c \in Replicas : \A e : CommitEntry(c, e) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF CommitEntry
<1>21. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF AdvertiseCommit
<1>22. \A r \in Replicas : \A m : LearnCommit(r, m) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF LearnCommit
<1>23. \A c \in Replicas : Activate(c) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF Activate
<1>24. \A r \in Replicas : \A e : ApplyEntry(r, e) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF ApplyEntry
<1>25. ASSUME NEW r \in Replicas, Crash(r)
      PROVE AckInboxOrigins'
    <2>1. r \in Replicas /\ ackInbox' = [ackInbox EXCEPT ![r] = {}]
        BY <1>25 DEF Crash
    <2> QED BY ONLY InboxResetOrigins, <1>0, <2>1
<1>26. \A r \in Replicas : Restart(r) => AckInboxOrigins'
    BY SMT, InboxUnchangedOrigins DEF Restart
<1> QED BY ONLY SMT, <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
    DEF ProtocolNext, AdministrativeNext

KnowledgeChangingNext ==
    \/ \E c \in Replicas : ConfirmProposal(c)
    \/ \E c \in Replicas : \E e : CommitEntry(c, e) \/ AdvertiseCommit(c, e)
    \/ \E r \in Replicas : \E m : LearnCommit(r, m)

THEOREM ProtocolKnowledgeProjection ==
    ProtocolNext => (KnowledgeChangingNext \/
                    UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
<1>1. \A c \in Replicas : StartElection(c) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF StartElection
<1>2. \A r \in Replicas : \A t : AdoptTerm(r, t) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF AdoptTerm
<1>3. \A r \in Replicas : \A req : GrantVote(r, req) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF GrantVote
<1>4. \A c \in Replicas : \A m : DeliverVote(c, m) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF DeliverVote
<1>5. \A c \in Replicas : WinElection(c) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF WinElection
<1>6. \A r \in Replicas : \A req : MakeReport(r, req) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF MakeReport
<1>7. \A c \in Replicas : \A m : DeliverReport(c, m) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF DeliverReport
<1>8. \A c \in Replicas : \A p : BuildRecovery(c, p) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF BuildRecovery
<1>9. \A c \in Replicas : \A v : CreateEntry(c, v) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF CreateEntry
<1>10. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF CreateSuccessor
<1>11. \A c \in Replicas : \A e : SendEntry(c, e) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF SendEntry
<1>12. \A r \in Replicas : \A o : ReceiveEntry(r, o) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF ReceiveEntry
<1>13. \A r \in Replicas : \A o : AckEntry(r, o) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF AckEntry
<1>14. \A r, s \in Replicas : \A p, e : CopyProposalEntry(r, s, p, e) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF CopyProposalEntry
<1>15. \A r \in Replicas : \A p : RetainProposal(r, p) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF RetainProposal
<1>16. \A r \in Replicas : \A p : AckProposal(r, p) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF AckProposal
<1>17. \A c \in Replicas : \A m : DeliverAck(c, m) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF DeliverAck
<1>18. \A c \in Replicas : ConfirmProposal(c) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF KnowledgeChangingNext
<1>19. \A r \in Replicas : \A p : LearnConfirmation(r, p) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF LearnConfirmation
<1>20. \A c \in Replicas : \A e : CommitEntry(c, e) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF KnowledgeChangingNext
<1>21. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF KnowledgeChangingNext
<1>22. \A r \in Replicas : \A m : LearnCommit(r, m) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF KnowledgeChangingNext
<1>23. \A c \in Replicas : Activate(c) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF Activate
<1>24. \A r \in Replicas : \A e : ApplyEntry(r, e) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF ApplyEntry
<1>25. \A r \in Replicas : Crash(r) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF Crash
<1>26. \A r \in Replicas : Restart(r) => (KnowledgeChangingNext \/
           UNCHANGED <<knownCommitted, commitMessages, confirmations>>)
    BY SMT DEF Restart
<1> QED BY ONLY ZenonT(10), <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
    DEF ProtocolNext, AdministrativeNext
=============================================================================
