-------------------------- MODULE TRaftCommitSupport -------------------------
EXTENDS TRaftCommitState, TRaftControlState, TRaftEvidenceProof, TRaftFunctionProof
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM QuorumIsNonempty ==
    ASSUME NEW S, Quorum(S)
    PROVE S # {}
<1>1. Cardinality({}) = 0 /\ Cardinality(Replicas) \in Nat
    BY FS_EmptySet, FS_CardinalityType
<1> QED BY SMT, <1>1 DEF Quorum

EpochEvidence(M, t) == {[epoch |-> t, entry |-> e] :
    e \in {x \in (UNION {a.contents : a \in M}) :
        \E c \in Replicas : Quorum(MessageAckers(M, c, t, x))}}

THEOREM EvidenceAsEpochUnion ==
    ASSUME NEW M
    PROVE Evidence(M) = (UNION {EpochEvidence(M, t) : t \in Terms \ {0}})
BY DEF Evidence, EpochEvidence

THEOREM QuorumCreatesIndependentEvidence ==
    ASSUME NEW M, NEW c \in Replicas, NEW t \in Terms \ {0}, NEW e,
           Quorum(MessageAckers(M, c, t, e))
    PROVE [epoch |-> t, entry |-> e] \in Evidence(M)
<1>1. MessageAckers(M, c, t, e) # {}
    BY QuorumIsNonempty
<1>2. e \in (UNION {a.contents : a \in M})
    BY SMT, <1>1 DEF MessageAckers
<1>3. c \in Replicas /\ t \in Terms \ {0} /\ Quorum(MessageAckers(M, c, t, e))
    OBVIOUS
<1>4. e \in {x \in (UNION {a.contents : a \in M}) :
                    \E owner \in Replicas : Quorum(MessageAckers(M, owner, t, x))}
    BY ONLY SMT, <1>2, <1>3
<1>5. [epoch |-> t, entry |-> e] \in EpochEvidence(M, t)
    BY ONLY SMT, <1>4 DEF EpochEvidence
<1>6. EpochEvidence(M, t) \in {EpochEvidence(M, u) : u \in Terms \ {0}}
    BY ONLY SMT, <1>3
<1> QED BY ONLY ZenonT(5), <1>5, <1>6, EvidenceAsEpochUnion

THEOREM ProposalQuorumMonotone ==
    ASSUME NEW A, NEW B, A \subseteq B, NEW p, Quorum(ProposalSenders(A, p))
    PROVE Quorum(ProposalSenders(B, p))
<1>1. ProposalSenders(A, p) \subseteq ProposalSenders(B, p)
    BY SMT DEF ProposalSenders
<1> QED BY SMT, <1>1, MajorityUpward DEF Quorum, Majority, ProposalSenders

THEOREM KnowledgeInitially == Init => KnowledgeInvariant
BY SMT DEF Init, KnowledgeInvariant, AckInboxOrigins, KnowledgeShape,
           CommittedKnowledgeSound, CommitMessageEvidence, ConfirmationHasQuorum

THEOREM KnowledgeStuttering ==
    ASSUME KnowledgeInvariant, UNCHANGED KnowledgeVars
    PROVE KnowledgeInvariant'
<1>1. ackInbox' = ackInbox /\ ackMessages' = ackMessages
      /\ knownCommitted' = knownCommitted /\ commitMessages' = commitMessages
      /\ commitHistory' = commitHistory /\ confirmations' = confirmations
    BY DEF KnowledgeVars
<1>2. KnowledgeInvariant
    OBVIOUS
<1> QED BY ONLY IsaM("auto"), <1>1, <1>2
    DEF KnowledgeInvariant, AckInboxOrigins, KnowledgeShape,
        CommittedKnowledgeSound, CommitMessageEvidence, ConfirmationHasQuorum

THEOREM ConfirmationEvidencePersists ==
    ASSUME ConfirmationHasQuorum, ackMessages \subseteq ackMessages',
           UNCHANGED confirmations
    PROVE ConfirmationHasQuorum'
<1>0. ackMessages \subseteq ackMessages'
    OBVIOUS
<1>1. ASSUME NEW p \in confirmations
      PROVE Quorum(ProposalSenders(ackMessages', p))
    <2>1. Quorum(ProposalSenders(ackMessages, p))
        BY <1>1 DEF ConfirmationHasQuorum, ProposalSenders
    <2> QED BY ONLY ProposalQuorumMonotone, <2>1, <1>0
<1> QED BY SMT, <1>1 DEF ConfirmationHasQuorum, ProposalSenders

THEOREM KnowledgeEvidencePersists ==
    ASSUME KnowledgeShape, CommittedKnowledgeSound, CommitMessageEvidence,
           commitHistory \subseteq commitHistory',
           UNCHANGED <<knownCommitted, commitMessages>>
    PROVE KnowledgeShape' /\ CommittedKnowledgeSound' /\ CommitMessageEvidence'
BY SMT DEF KnowledgeShape, CommittedKnowledgeSound, CommitMessageEvidence

THEOREM InboxUnchangedOrigins ==
    ASSUME AckInboxOrigins, ackMessages \subseteq ackMessages', UNCHANGED ackInbox
    PROVE AckInboxOrigins'
BY SMT DEF AckInboxOrigins

THEOREM InboxResetOrigins ==
    ASSUME AckInboxOrigins, ackMessages \subseteq ackMessages', NEW r \in Replicas,
           ackInbox' = [ackInbox EXCEPT ![r] = {}]
    PROVE AckInboxOrigins'
BY SMT DEF AckInboxOrigins

THEOREM InboxReceiveOrigins ==
    ASSUME AckInboxOrigins, ackMessages \subseteq ackMessages', NEW r \in Replicas,
           NEW m \in ackMessages, ackInbox' = [ackInbox EXCEPT ![r] = @ \cup {m}]
    PROVE AckInboxOrigins'
BY SMT DEF AckInboxOrigins
=============================================================================
