-------------------- MODULE TRaftCanonicalLeaderFrames -----------------------
EXTENDS TRaftCanonicalTransitionSupport

LeaderData == /\ term \in [Replicas -> Terms] /\ role \in [Replicas -> Roles]
              /\ formal \in [Replicas -> SUBSET Entries]
              /\ \A r \in Replicas : role[r] = "Leader" => formal[r] \subseteq canonical[term[r]]
PostLeaderBound == \A r \in Replicas : role'[r] = "Leader" => formal'[r] \subseteq canonical[term'[r]]
NormalCreation == (\E c \in Replicas : \E v : CreateEntry(c, v))
               \/ (\E c \in Replicas : \E v, k : CreateSuccessor(c, v, k))

THEOREM CandidateHasLeaderData == ProofInvariant => LeaderData
BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape, LeaderData

THEOREM ActivationKeepsCanonicalBound ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, Activate(c)
    PROVE PostLeaderBound
<1>1. LeaderData /\ formal[c] = canonical[term[c]]
    BY CandidateHasLeaderData, ActivationAlreadyHasFullCanonicalLog
<1> QED BY SMT, <1>1 DEF Activate, LeaderData, PostLeaderBound

THEOREM ReceiptKeepsCanonicalBound ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
    PROVE PostLeaderBound
<1>1. LeaderData
    BY CandidateHasLeaderData
<1>2. role[r] = "Leader" => formal' = formal
    BY ExistingLeaderIgnoresOwnOffer
<1> QED BY SMT, <1>1, <1>2 DEF ReceiveEntry, LeaderData, PostLeaderBound

THEOREM LearningKeepsCanonicalBound ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
    PROVE PostLeaderBound
<1>1. LeaderData
    BY CandidateHasLeaderData
<1>2. role[r] = "Leader" => formal' = formal
    BY ExistingLeaderIgnoresOwnConfirmation
<1> QED BY SMT, <1>1, <1>2 DEF LearnConfirmation, LeaderData, PostLeaderBound

THEOREM AdministrativeActionsKeepLeaderCanonicalBound ==
    ASSUME ProofInvariant, ElectionSafety, AdministrativeNext
    PROVE PostLeaderBound
<1>0. LeaderData
    BY CandidateHasLeaderData
<1>1. ASSUME NEW c \in Replicas, StartElection(c)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>1 DEF StartElection, LeaderData, PostLeaderBound
<1>2. ASSUME NEW r \in Replicas, NEW t, AdoptTerm(r, t)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>2 DEF AdoptTerm, LeaderData, PostLeaderBound
<1>3. ASSUME NEW r \in Replicas, NEW req, GrantVote(r, req)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>3 DEF GrantVote, LeaderData, PostLeaderBound
<1>4. ASSUME NEW c \in Replicas, NEW m, DeliverVote(c, m)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>4 DEF DeliverVote, LeaderData, PostLeaderBound
<1>5. ASSUME NEW c \in Replicas, WinElection(c)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>5 DEF WinElection, LeaderData, PostLeaderBound
<1>6. ASSUME NEW r \in Replicas, NEW req, MakeReport(r, req)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>6 DEF MakeReport, LeaderData, PostLeaderBound
<1>7. ASSUME NEW c \in Replicas, NEW m, DeliverReport(c, m)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>7 DEF DeliverReport, LeaderData, PostLeaderBound
<1>8. ASSUME NEW c \in Replicas, NEW p, BuildRecovery(c, p)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>8 DEF BuildRecovery, LeaderData, PostLeaderBound
<1>9. ASSUME NEW c \in Replicas, NEW e, SendEntry(c, e)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>9 DEF SendEntry, LeaderData, PostLeaderBound
<1>10. ASSUME NEW r \in Replicas, NEW o, AckEntry(r, o)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>10 DEF AckEntry, LeaderData, PostLeaderBound
<1>11. ASSUME NEW r \in Replicas, NEW s, NEW p, NEW e, CopyProposalEntry(r, s, p, e)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>11 DEF CopyProposalEntry, LeaderData, PostLeaderBound
<1>12. ASSUME NEW r \in Replicas, NEW p, RetainProposal(r, p)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>12 DEF RetainProposal, LeaderData, PostLeaderBound
<1>13. ASSUME NEW r \in Replicas, NEW p, AckProposal(r, p)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>13 DEF AckProposal, LeaderData, PostLeaderBound
<1>14. ASSUME NEW c \in Replicas, NEW m, DeliverAck(c, m)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>14 DEF DeliverAck, LeaderData, PostLeaderBound
<1>15. ASSUME NEW c \in Replicas, ConfirmProposal(c)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>15 DEF ConfirmProposal, LeaderData, PostLeaderBound
<1>16. ASSUME NEW c \in Replicas, NEW e, CommitEntry(c, e)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>16 DEF CommitEntry, LeaderData, PostLeaderBound
<1>17. ASSUME NEW c \in Replicas, NEW e, AdvertiseCommit(c, e)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>17 DEF AdvertiseCommit, LeaderData, PostLeaderBound
<1>18. ASSUME NEW r \in Replicas, NEW m, LearnCommit(r, m)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>18 DEF LearnCommit, LeaderData, PostLeaderBound
<1>19. ASSUME NEW r \in Replicas, NEW e, ApplyEntry(r, e)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>19 DEF ApplyEntry, LeaderData, PostLeaderBound
<1>20. ASSUME NEW r \in Replicas, Crash(r)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>20 DEF Crash, LeaderData, PostLeaderBound
<1>21. ASSUME NEW r \in Replicas, Restart(r)
      PROVE PostLeaderBound
    BY SMT, <1>0, <1>21 DEF Restart, LeaderData, PostLeaderBound
<1> QED BY SMT, ActivationKeepsCanonicalBound, ReceiptKeepsCanonicalBound, LearningKeepsCanonicalBound, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
    DEF AdministrativeNext

THEOREM OnlyNormalCreationExtendsLeaderCanonical ==
    ASSUME ProofInvariant, ElectionSafety, ProtocolNext
    PROVE NormalCreation \/ PostLeaderBound
<1>1. AdministrativeNext => PostLeaderBound
    BY AdministrativeActionsKeepLeaderCanonicalBound
<1>2. (\E r \in Replicas : \E e : ApplyEntry(r, e)) => PostLeaderBound
    BY SMT, CandidateHasLeaderData DEF ApplyEntry, LeaderData, PostLeaderBound
<1> QED BY <1>1, <1>2 DEF ProtocolNext, NormalCreation
=============================================================================
