-------------------------- MODULE TRaftCommitActions -------------------------
EXTENDS TRaftCommitSupport

THEOREM KnowledgeInsertPreservesEvidence ==
    ASSUME KnowledgeShape, CommittedKnowledgeSound, commitHistory \subseteq commitHistory',
           NEW r \in Replicas, NEW e,
           \E f \in commitHistory' : f.entry = e,
           knownCommitted' = [knownCommitted EXCEPT ![r] = @ \cup {e}]
    PROVE KnowledgeShape' /\ CommittedKnowledgeSound'
<1>1. KnowledgeShape'
    BY SMT, FunctionUpdatePreservesDomainShape DEF KnowledgeShape
<1>2. CommittedKnowledgeSound'
    <2>1. \A checkedNode \in Replicas :
              knownCommitted'[checkedNode] \subseteq knownCommitted[checkedNode] \cup {e}
        BY SMT DEF KnowledgeShape
    <2>2. \A checkedNode \in Replicas : \A oldEntry \in knownCommitted[checkedNode] :
              \E fact \in commitHistory' : fact.entry = oldEntry
        BY SMT DEF CommittedKnowledgeSound
    <2>3. \E fact \in commitHistory' : fact.entry = e
        OBVIOUS
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3 DEF CommittedKnowledgeSound
<1> QED BY <1>1, <1>2

THEOREM CommitEntryHasEvidence ==
    ASSUME ElectionInvariant, AckInboxOrigins, ~MutNoCommitQuorum,
           NEW c \in Replicas, NEW e, CommitEntry(c, e),
           ackMessages \subseteq ackMessages', Observe
    PROVE \E f \in commitHistory' : f.entry = e
<1>1. c \in Replicas /\ term[c] \in Terms \ {0}
      /\ Quorum(MessageAckers(ackInbox[c], c, term[c], e))
      /\ ackInbox[c] \subseteq ackMessages'
    BY SMT DEF ElectionInvariant, ElectionTypes, AckInboxOrigins, CommitEntry, Ackers
<1>2. Quorum(MessageAckers(ackMessages', c, term[c], e))
    BY AckQuorumMonotone, <1>1
<1>3. [epoch |-> term[c], entry |-> e] \in Evidence(ackMessages')
    BY QuorumCreatesIndependentEvidence, <1>1, <1>2
<1> QED BY SMT, <1>3 DEF Observe

THEOREM CommitEntryPreservesKnowledge ==
    ASSUME ElectionInvariant, KnowledgeInvariant, CommitFaultsDisabled,
           NEW c \in Replicas, NEW e, CommitEntry(c, e),
           ackMessages \subseteq ackMessages', commitHistory \subseteq commitHistory', Observe
    PROVE KnowledgeShape' /\ CommittedKnowledgeSound' /\ CommitMessageEvidence'
<1>1. \E f \in commitHistory' : f.entry = e
    BY CommitEntryHasEvidence DEF KnowledgeInvariant, CommitFaultsDisabled
<1>2. KnowledgeShape' /\ CommittedKnowledgeSound'
    BY KnowledgeInsertPreservesEvidence, <1>1 DEF KnowledgeInvariant, CommitEntry
<1>3. CommitMessageEvidence'
    BY SMT, <1>1 DEF KnowledgeInvariant, CommitMessageEvidence, CommitEntry
<1> QED BY <1>2, <1>3

THEOREM LearnCommitPreservesKnowledge ==
    ASSUME KnowledgeInvariant, NEW r \in Replicas, NEW m, LearnCommit(r, m),
           commitHistory \subseteq commitHistory'
    PROVE KnowledgeShape' /\ CommittedKnowledgeSound' /\ CommitMessageEvidence'
<1>1. \E f \in commitHistory' : f.entry = m.entry
    BY SMT DEF KnowledgeInvariant, CommitMessageEvidence, LearnCommit
<1>2. KnowledgeShape' /\ CommittedKnowledgeSound'
    BY KnowledgeInsertPreservesEvidence, <1>1 DEF KnowledgeInvariant, LearnCommit
<1>3. CommitMessageEvidence'
    BY SMT DEF KnowledgeInvariant, CommitMessageEvidence, LearnCommit
<1> QED BY <1>2, <1>3

THEOREM AdvertiseCommitPreservesKnowledge ==
    ASSUME KnowledgeInvariant, NEW c \in Replicas, NEW e, AdvertiseCommit(c, e),
           commitHistory \subseteq commitHistory'
    PROVE KnowledgeShape' /\ CommittedKnowledgeSound' /\ CommitMessageEvidence'
<1>1. \E f \in commitHistory' : f.entry = e
    BY SMT DEF KnowledgeInvariant, CommittedKnowledgeSound, AdvertiseCommit
<1>2. KnowledgeShape' /\ CommittedKnowledgeSound'
    BY SMT DEF KnowledgeInvariant, KnowledgeShape, CommittedKnowledgeSound, AdvertiseCommit
<1>3. CommitMessageEvidence'
    BY SMT, <1>1 DEF KnowledgeInvariant, CommitMessageEvidence, AdvertiseCommit
<1> QED BY <1>2, <1>3

THEOREM ConfirmProposalPreservesCertificate ==
    ASSUME ControlInvariant, KnowledgeInvariant, ~MutEarlyPublish,
           NEW c \in Replicas, ConfirmProposal(c), ackMessages \subseteq ackMessages'
    PROVE ConfirmationHasQuorum'
<1>0. phase[c] = "sync" /\ c \in Replicas /\ ackMessages \subseteq ackMessages'
      /\ Quorum(ProposalAckers(c, current[c]))
      /\ ackInbox[c] \subseteq ackMessages'
    BY SMT DEF ConfirmProposal, KnowledgeInvariant, AckInboxOrigins
<1>01. current[c].owner = c
    BY SMT, <1>0 DEF ControlInvariant, ControlShape
<1>1. current[c].owner = c
      /\ Quorum(ProposalSenders(ackInbox[c], current[c]))
      /\ ackInbox[c] \subseteq ackMessages'
    BY ONLY IsaM("auto"), <1>0, <1>01 DEF ProposalAckers, ProposalSenders
<1>2. Quorum(ProposalSenders(ackMessages', current[c]))
    BY ProposalQuorumMonotone, <1>1
<1>3. \A p \in confirmations : Quorum(ProposalSenders(ackMessages', p))
    <2>1. ASSUME NEW p \in confirmations
          PROVE Quorum(ProposalSenders(ackMessages', p))
        <3>1. Quorum(ProposalSenders(ackMessages, p))
            BY <2>1 DEF KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders
        <3> QED BY ONLY ProposalQuorumMonotone, <1>0, <3>1
    <2> QED BY <2>1
<1>4. confirmations' = confirmations \cup {current[c]}
    BY DEF ConfirmProposal
<1> QED BY ONLY IsaM("auto"), <1>2, <1>3, <1>4
    DEF ConfirmationHasQuorum, ProposalSenders
=============================================================================
