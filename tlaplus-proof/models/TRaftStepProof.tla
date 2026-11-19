--------------------------- MODULE TRaftStepProof ----------------------------
EXTENDS TRaftProofState, TRaftQuorumProof, TLAPS
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation
StepTypes == /\ term \in [Replicas -> Nat]
             /\ stored \in [Replicas -> SUBSET Entries]
             /\ formal \in [Replicas -> SUBSET Entries]
StepFacts == /\ \A r \in Replicas : term[r] <= term'[r]
             /\ ackMessages \subseteq ackMessages'
             /\ \A r \in Replicas : stored[r] \subseteq stored'[r]
             /\ \A a \in ackMessages' \ ackMessages :
                   a.sender \in Replicas /\ a.epoch = term[a.sender]
THEOREM EveryProtocolStepHasFacts ==
    ASSUME StepTypes, Terms \subseteq Nat, ProtocolNext,
           \A p \in proposals : p.prefix \subseteq Entries /\ p.first \in Entries,
           \A r \in Replicas : retained[r] \subseteq proposals,
           \A c \in Replicas : ReportedProposals(c) \subseteq proposals
    PROVE StepFacts
<1>1. \A c \in Replicas : StartElection(c) => StepFacts
    BY SMT DEF StartElection, StepTypes, StepFacts, Ack
<1>2. \A r \in Replicas, t \in Terms : AdoptTerm(r, t) => StepFacts
    BY SMTT(20) DEF AdoptTerm, StepTypes, StepFacts, Ack
<1>3. \A r \in Replicas, req \in voteRequests : GrantVote(r, req) => StepFacts
    BY SMT DEF GrantVote, StepTypes, StepFacts, Ack
<1>4. \A c \in Replicas, m \in voteMessages : DeliverVote(c, m) => StepFacts
    BY SMT DEF DeliverVote, StepTypes, StepFacts, Ack
<1>5. \A c \in Replicas : WinElection(c) => StepFacts
    BY SMT DEF WinElection, StepTypes, StepFacts, Ack
<1>6. \A r \in Replicas, req \in recoveryRequests : MakeReport(r, req) => StepFacts
    BY SMT DEF MakeReport, StepTypes, StepFacts, Ack
<1>7. \A c \in Replicas, m \in reportMessages : DeliverReport(c, m) => StepFacts
    BY SMT DEF DeliverReport, StepTypes, StepFacts, Ack
<1>8. \A c \in Replicas, p \in proposals \cup {NoProposal} : BuildRecovery(c, p) => StepFacts
    BY SMT DEF BuildRecovery, StepTypes, StepFacts, Ack
<1>9. \A c \in Replicas, v \in DataValues : CreateEntry(c, v) => StepFacts
    BY SMT DEF CreateEntry, StepTypes, StepFacts, Ack
<1>10. \A c \in Replicas, v \in DataValues \cup {NoValue}, k \in {"data", "noop"} : CreateSuccessor(c, v, k) => StepFacts
    BY SMT DEF CreateSuccessor, StepTypes, StepFacts, Ack
<1>11. \A c \in Replicas, e \in Entries : SendEntry(c, e) => StepFacts
    BY SMT DEF SendEntry, StepTypes, StepFacts, Ack
<1>12. \A r \in Replicas, o \in offers : ReceiveEntry(r, o) => StepFacts
    BY SMT DEF ReceiveEntry, StepTypes, StepFacts, Ack
<1>13. \A r \in Replicas, o \in offers : AckEntry(r, o) => StepFacts
    BY SMT DEF AckEntry, StepTypes, StepFacts, Ack
<1>14. \A r, source \in Replicas, p \in proposals, e \in Entries : CopyProposalEntry(r, source, p, e) => StepFacts
    BY SMT DEF CopyProposalEntry, StepTypes, StepFacts, Ack
<1>15. \A r \in Replicas, p \in proposals : RetainProposal(r, p) => StepFacts
    BY SMT DEF RetainProposal, StepTypes, StepFacts, Ack
<1>16. \A r \in Replicas, p \in proposals : AckProposal(r, p) => StepFacts
    BY SMT DEF AckProposal, StepTypes, StepFacts, Ack
<1>17. \A c \in Replicas, m \in ackMessages : DeliverAck(c, m) => StepFacts
    BY SMT DEF DeliverAck, StepTypes, StepFacts, Ack
<1>18. \A c \in Replicas : ConfirmProposal(c) => StepFacts
    BY SMT DEF ConfirmProposal, StepTypes, StepFacts, Ack
<1>19. \A r \in Replicas, p \in confirmations : LearnConfirmation(r, p) => StepFacts
    BY SMT DEF LearnConfirmation, StepTypes, StepFacts, Ack
<1>20. \A c \in Replicas, e \in Entries : CommitEntry(c, e) => StepFacts
    BY SMT DEF CommitEntry, StepTypes, StepFacts, Ack
<1>21. \A c \in Replicas, e \in Entries : AdvertiseCommit(c, e) => StepFacts
    BY SMT DEF AdvertiseCommit, StepTypes, StepFacts, Ack
<1>22. \A r \in Replicas, m \in commitMessages : LearnCommit(r, m) => StepFacts
    BY SMT DEF LearnCommit, StepTypes, StepFacts, Ack
<1>23. \A c \in Replicas : Activate(c) => StepFacts
    BY SMT DEF Activate, StepTypes, StepFacts, Ack
<1>24. \A r \in Replicas, e \in Entries : ApplyEntry(r, e) => StepFacts
    BY SMT DEF ApplyEntry, StepTypes, StepFacts, Ack
<1>25. \A r \in Replicas : Crash(r) => StepFacts
    BY SMT DEF Crash, StepTypes, StepFacts, Ack
<1>26. \A r \in Replicas : Restart(r) => StepFacts
    BY SMT DEF Restart, StepTypes, StepFacts, Ack
<1> QED BY SMTT(20), <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
    DEF ProtocolNext, AdministrativeNext, Latest, Result, StepTypes

=============================================================================
