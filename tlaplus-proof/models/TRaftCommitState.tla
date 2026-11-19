--------------------------- MODULE TRaftCommitState --------------------------
EXTENDS TRaftCore

\* Proof predicates only; protocol decisions use the existing local inboxes.
AckInboxOrigins == ackInbox \in [Replicas -> SUBSET ackMessages]
CommitMessageEvidence == \A m \in commitMessages :
    \E fact \in commitHistory : fact.entry = m.entry
KnowledgeShape == knownCommitted = [r \in Replicas |-> knownCommitted[r]]
KnowledgeInvariant == /\ AckInboxOrigins /\ KnowledgeShape
                      /\ CommittedKnowledgeSound /\ CommitMessageEvidence
                      /\ ConfirmationHasQuorum
KnowledgeVars == <<ackInbox, ackMessages, knownCommitted, commitMessages,
                   commitHistory, confirmations>>
CommitFaultsDisabled == ~MutNoCommitQuorum /\ ~MutEarlyPublish
ProposalSenders(M, p) ==
    {r \in Replicas : Ack(r, p.owner, p.epoch, p.first, Result(p)) \in M}
=============================================================================
