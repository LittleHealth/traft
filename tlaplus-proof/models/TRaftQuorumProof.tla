-------------------------- MODULE TRaftQuorumProof ---------------------------
EXTENDS Integers, FiniteSetTheorems, TLAPS

Majority(N, Q) == Q \subseteq N /\ 2 * Cardinality(Q) > Cardinality(N)
Senders(N, M, t, e) == {r \in N : \E a \in M :
                              a.sender = r /\ a.epoch = t /\ e \in a.contents}
Possible(N, M, promise, t, e) == Senders(N, M, t, e) \cup
                                   {r \in N : promise[r] <= t}

THEOREM MajorityIntersection ==
    ASSUME NEW N, NEW A, NEW B, IsFiniteSet(N), Majority(N, A), Majority(N, B)
    PROVE A \cap B # {}
<1>1. IsFiniteSet(A) /\ IsFiniteSet(B)
    BY SMT, FS_Subset DEF Majority
<1>2. Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(N) \in Nat
    BY SMT, <1>1, FS_CardinalityType
<1>3. Cardinality(A) + Cardinality(B) > Cardinality(N)
    BY SMT, <1>2 DEF Majority
<1> QED BY SMT, <1>3, FS_MajoritiesIntersect DEF Majority

THEOREM MajorityUpward ==
    ASSUME NEW N, NEW A, NEW B, IsFiniteSet(N), Majority(N, A),
           A \subseteq B, B \subseteq N
    PROVE Majority(N, B)
<1>1. IsFiniteSet(A) /\ IsFiniteSet(B)
    BY SMT, FS_Subset DEF Majority
<1>2. Cardinality(A) <= Cardinality(B)
    BY SMT, <1>1, FS_Subset
<1>3. Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(N) \in Nat
    BY SMT, <1>1, FS_CardinalityType
<1> QED BY SMT, <1>2, <1>3 DEF Majority

THEOREM CountCompleteness ==
    ASSUME NEW LeaderSet, NEW FollowerSet, IsFiniteSet(LeaderSet),
           FollowerSet \subseteq LeaderSet,
           Cardinality(FollowerSet) = Cardinality(LeaderSet)
    PROVE FollowerSet = LeaderSet
BY SMT, FS_Subset

\* New ACKs can replace a still-eligible sender, but cannot create an extra
\* eligible sender. Therefore possible old-term majorities only shrink.
THEOREM PossibleAckersShrink ==
    ASSUME NEW N, NEW oldMessages, NEW newMessages,
           NEW before \in [N -> Nat], NEW after \in [N -> Nat],
           NEW t \in Nat, NEW e,
           \A r \in N : before[r] <= after[r],
           \A a \in newMessages \ oldMessages :
               a.sender \in N /\ a.epoch = before[a.sender]
    PROVE Possible(N, newMessages, after, t, e)
              \subseteq Possible(N, oldMessages, before, t, e)
BY SMT DEF Possible, Senders

THEOREM ReportQuorumHasOldAck ==
    ASSUME NEW N, NEW reports, NEW messages, NEW promise \in [N -> Nat],
           NEW t \in Nat, NEW e, IsFiniteSet(N), Majority(N, reports),
           Majority(N, Possible(N, messages, promise, t, e)),
           \A r \in reports : promise[r] > t
    PROVE \E r \in reports : r \in Senders(N, messages, t, e)
<1>1. reports \cap Possible(N, messages, promise, t, e) # {}
    BY SMT, MajorityIntersection
<1> QED BY SMT, <1>1 DEF Possible, Senders

THEOREM AckedEntriesArePossible ==
    ASSUME NEW N, NEW Q, NEW M, NEW promise, NEW t, NEW e,
           IsFiniteSet(N), Majority(N, Q), Q \subseteq Senders(N, M, t, e)
    PROVE Majority(N, Possible(N, M, promise, t, e))
BY SMT, MajorityUpward DEF Possible, Senders
=============================================================================
