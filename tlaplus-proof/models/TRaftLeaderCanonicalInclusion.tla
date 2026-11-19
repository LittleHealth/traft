------------------- MODULE TRaftLeaderCanonicalInclusion --------------------
EXTENDS TRaftCanonicalUpdateProof

PostLeaderIncludesOldCanonical == \A r \in Replicas :
    role'[r] = "Leader" => canonical[term'[r]] \subseteq formal'[r]

THEOREM PostLeadersContainOldCanonical ==
    ASSUME ProofInvariant, ElectionSafety, ProtocolNext
    PROVE PostLeaderIncludesOldCanonical
<1>0. formal \in [Replicas -> SUBSET Entries] /\ term \in [Replicas -> Terms]
      /\ role \in [Replicas -> Roles]
      /\ (\A r \in Replicas : role[r] = "Leader" => formal[r] = canonical[term[r]])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>1. ASSUME NEW c \in Replicas, StartElection(c)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>1 DEF StartElection, PostLeaderIncludesOldCanonical
<1>2. ASSUME NEW r \in Replicas, NEW t, AdoptTerm(r, t)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>2 DEF AdoptTerm, PostLeaderIncludesOldCanonical
<1>3. ASSUME NEW r \in Replicas, NEW req, GrantVote(r, req)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>3 DEF GrantVote, PostLeaderIncludesOldCanonical
<1>4. ASSUME NEW c \in Replicas, NEW m, DeliverVote(c, m)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>4 DEF DeliverVote, PostLeaderIncludesOldCanonical
<1>5. ASSUME NEW c \in Replicas, WinElection(c)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>5 DEF WinElection, PostLeaderIncludesOldCanonical
<1>6. ASSUME NEW r \in Replicas, NEW req, MakeReport(r, req)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>6 DEF MakeReport, PostLeaderIncludesOldCanonical
<1>7. ASSUME NEW c \in Replicas, NEW m, DeliverReport(c, m)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>7 DEF DeliverReport, PostLeaderIncludesOldCanonical
<1>8. ASSUME NEW c \in Replicas, NEW p, BuildRecovery(c, p)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>8 DEF BuildRecovery, PostLeaderIncludesOldCanonical
<1>9. ASSUME NEW c \in Replicas, NEW v, CreateEntry(c, v)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>9 DEF CreateEntry, PostLeaderIncludesOldCanonical
<1>10. ASSUME NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>10 DEF CreateSuccessor, PostLeaderIncludesOldCanonical
<1>11. ASSUME NEW c \in Replicas, NEW e, SendEntry(c, e)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>11 DEF SendEntry, PostLeaderIncludesOldCanonical
<1>12. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>12 DEF ReceiveEntry, PostLeaderIncludesOldCanonical
<1>13. ASSUME NEW r \in Replicas, NEW o, AckEntry(r, o)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>13 DEF AckEntry, PostLeaderIncludesOldCanonical
<1>14. ASSUME NEW r \in Replicas, NEW s \in Replicas, NEW p, NEW e, CopyProposalEntry(r, s, p, e)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>14 DEF CopyProposalEntry, PostLeaderIncludesOldCanonical
<1>15. ASSUME NEW r \in Replicas, NEW p, RetainProposal(r, p)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>15 DEF RetainProposal, PostLeaderIncludesOldCanonical
<1>16. ASSUME NEW r \in Replicas, NEW p, AckProposal(r, p)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>16 DEF AckProposal, PostLeaderIncludesOldCanonical
<1>17. ASSUME NEW c \in Replicas, NEW m, DeliverAck(c, m)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>17 DEF DeliverAck, PostLeaderIncludesOldCanonical
<1>18. ASSUME NEW c \in Replicas, ConfirmProposal(c)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>18 DEF ConfirmProposal, PostLeaderIncludesOldCanonical
<1>19. ASSUME NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
      PROVE PostLeaderIncludesOldCanonical
    <2>1. role[r] = "Leader" => formal' = formal
        BY ExistingLeaderIgnoresOwnConfirmation, <1>19
    <2> QED BY SMT, <1>0, <1>19, <2>1 DEF LearnConfirmation, PostLeaderIncludesOldCanonical
<1>20. ASSUME NEW c \in Replicas, NEW e, CommitEntry(c, e)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>20 DEF CommitEntry, PostLeaderIncludesOldCanonical
<1>21. ASSUME NEW c \in Replicas, NEW e, AdvertiseCommit(c, e)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>21 DEF AdvertiseCommit, PostLeaderIncludesOldCanonical
<1>22. ASSUME NEW r \in Replicas, NEW m, LearnCommit(r, m)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>22 DEF LearnCommit, PostLeaderIncludesOldCanonical
<1>23. ASSUME NEW c \in Replicas, Activate(c)
      PROVE PostLeaderIncludesOldCanonical
    <2>1. formal[c] = canonical[term[c]]
        BY ActivationAlreadyHasFullCanonicalLog, <1>23
    <2> QED BY SMT, <1>0, <1>23, <2>1 DEF Activate, PostLeaderIncludesOldCanonical
<1>24. ASSUME NEW r \in Replicas, NEW e, ApplyEntry(r, e)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>24 DEF ApplyEntry, PostLeaderIncludesOldCanonical
<1>25. ASSUME NEW r \in Replicas, Crash(r)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>25 DEF Crash, PostLeaderIncludesOldCanonical
<1>26. ASSUME NEW r \in Replicas, Restart(r)
      PROVE PostLeaderIncludesOldCanonical
    BY SMT, <1>0, <1>26 DEF Restart, PostLeaderIncludesOldCanonical
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26 DEF ProtocolNext, AdministrativeNext
=============================================================================
