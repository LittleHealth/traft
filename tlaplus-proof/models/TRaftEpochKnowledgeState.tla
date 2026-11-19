----------------------- MODULE TRaftEpochKnowledgeState ----------------------
EXTENDS TRaftCore

\* Bounds the authorizing epoch of locally known evidence. These predicates
\* observe protocol state; they never enable receipt, commitment, or recovery.
KnownBy(H, t, e) == \E f \in H :
    f.entry = e /\ f.epoch \in Nat /\ f.epoch <= t
KnowledgeAt(K, T, H) == \A r \in Replicas : \A e \in K[r] : KnownBy(H, T[r], e)
NotificationsAt(M, H) == \A m \in M : KnownBy(H, m.epoch, m.entry)
EpochKnowledgeInvariant ==
    /\ KnowledgeAt(knownCommitted, term, commitHistory)
    /\ NotificationsAt(commitMessages, commitHistory)
=============================================================================
