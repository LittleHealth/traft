----------------------- MODULE TRaftEpochKnowledgeProof ----------------------
EXTENDS TRaftEpochKnowledgeState, TRaftCommitTemporal
USE ParameterAssumptions, CommitProofFaultsDisabled
    DEF ParameterAssumptions, CommitProofFaultsDisabled, CommitFaultsDisabled

THEOREM ElectionStepNeverDecreasesTerms ==
    ASSUME ElectionInvariant, ProtocolNext
    PROVE \A r \in Replicas : term[r] <= term'[r]
<1>1. ElectionChangingNext \/ UNCHANGED ElectionCoreVars
    BY ProtocolElectionProjection
<1>2. term \in [Replicas -> Nat]
    BY SMT DEF ElectionInvariant, ElectionTypes, Terms
<1>3. \A c \in Replicas : StartElection(c) => \A r \in Replicas : term[r] <= term'[r]
    BY ONLY SMT, <1>2 DEF StartElection
<1>40. Terms \subseteq Nat
    OBVIOUS
<1>4. \A c \in Replicas, t \in Terms : AdoptTerm(c, t) => \A r \in Replicas : term[r] <= term'[r]
    BY ONLY SMT, <1>2, <1>40 DEF AdoptTerm
<1>5. (UNCHANGED term) => \A r \in Replicas : term[r] <= term'[r]
    BY ONLY SMT, <1>2
<1>6. \A c \in Replicas : (WinElection(c) \/ Activate(c) \/ Crash(c)) => UNCHANGED term
    BY ONLY SMT DEF WinElection, Activate, Crash
<1>7. \A r \in Replicas : \A req : GrantVote(r, req) => UNCHANGED term
    BY ONLY SMT DEF GrantVote
<1>8. \A c \in Replicas : \A m : DeliverVote(c, m) => UNCHANGED term
    BY ONLY SMT DEF DeliverVote
<1>9. UNCHANGED ElectionCoreVars => UNCHANGED term
    BY ONLY SMT DEF ElectionCoreVars
<1> QED BY ONLY ZenonT(10), <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
    DEF ElectionChangingNext

THEOREM KnownEvidenceSurvives ==
    ASSUME NEW H, NEW J, H \subseteq J, NEW t \in Nat, NEW u \in Nat,
           t <= u, NEW e, KnownBy(H, t, e)
    PROVE KnownBy(J, u, e)
BY SMT DEF KnownBy

THEOREM EpochKnowledgeFrame ==
    ASSUME EpochKnowledgeInvariant, term \in [Replicas -> Nat], term' \in [Replicas -> Nat],
           \A r \in Replicas : term[r] <= term'[r], commitHistory \subseteq commitHistory'
    PROVE KnowledgeAt(knownCommitted, term', commitHistory')
          /\ NotificationsAt(commitMessages, commitHistory')
BY SMT, KnownEvidenceSurvives DEF EpochKnowledgeInvariant, KnowledgeAt, NotificationsAt, KnownBy

THEOREM KnowledgeAtInsertion ==
    ASSUME NEW K, NEW T, NEW H, NEW r \in Replicas, NEW e,
           K = [node \in Replicas |-> K[node]],
           KnowledgeAt(K, T, H), KnownBy(H, T[r], e)
    PROVE KnowledgeAt([K EXCEPT ![r] = @ \cup {e}], T, H)
<1>1. ASSUME NEW s \in Replicas, NEW x \in [K EXCEPT ![r] = @ \cup {e}][s]
      PROVE KnownBy(H, T[s], x)
    <2>1. CASE s = r
        BY SMT, <1>1, <2>1 DEF KnowledgeAt
    <2>2. CASE s # r
        BY SMT, <1>1, <2>2 DEF KnowledgeAt
    <2> QED BY <2>1, <2>2
<1> QED BY ONLY <1>1 DEF KnowledgeAt

THEOREM CommitEntryIssuesEpochEvidence ==
    ASSUME ElectionInvariant, AckInboxOrigins, ~MutNoCommitQuorum,
           NEW c \in Replicas, NEW e, CommitEntry(c, e),
           ackMessages \subseteq ackMessages', Observe
    PROVE KnownBy(commitHistory', term[c], e)
<1>1. c \in Replicas /\ term[c] \in Terms \ {0} /\ term[c] \in Nat
      /\ Quorum(MessageAckers(ackInbox[c], c, term[c], e))
      /\ ackInbox[c] \subseteq ackMessages'
    BY SMT DEF ElectionInvariant, ElectionTypes, AckInboxOrigins, CommitEntry, Ackers, Terms
<1>2. Quorum(MessageAckers(ackMessages', c, term[c], e))
    BY AckQuorumMonotone, <1>1
<1>3. [epoch |-> term[c], entry |-> e] \in Evidence(ackMessages')
    BY QuorumCreatesIndependentEvidence, <1>1, <1>2
<1>4. [epoch |-> term[c], entry |-> e] \in commitHistory'
    BY SMT, <1>3 DEF Observe
<1> QED BY ONLY SMT, <1>1, <1>4 DEF KnownBy

THEOREM CommitEntryPreservesEpochKnowledge ==
    ASSUME ElectionInvariant, AckInboxOrigins, KnowledgeShape, ~MutNoCommitQuorum,
           NEW c \in Replicas, NEW e, CommitEntry(c, e),
           ackMessages \subseteq ackMessages', Observe,
           KnowledgeAt(knownCommitted, term', commitHistory'),
           NotificationsAt(commitMessages, commitHistory')
    PROVE EpochKnowledgeInvariant'
<1>0. KnowledgeShape
    OBVIOUS
<1>1. KnownBy(commitHistory', term[c], e)
    BY CommitEntryIssuesEpochEvidence
<1>2. term' = term /\ knownCommitted' = [knownCommitted EXCEPT ![c] = @ \cup {e}]
      /\ commitMessages' = commitMessages \cup {[owner |-> c, epoch |-> term[c], entry |-> e]}
    BY DEF CommitEntry
<1>3. KnowledgeAt(knownCommitted, term', commitHistory')
      /\ NotificationsAt(commitMessages, commitHistory') /\ c \in Replicas
    OBVIOUS
<1>4. KnowledgeAt(knownCommitted', term', commitHistory')
    BY ONLY SMT, KnowledgeAtInsertion, <1>0, <1>1, <1>2, <1>3 DEF KnowledgeShape
<1>5. NotificationsAt(commitMessages', commitHistory')
    BY ONLY SMT, <1>1, <1>2, <1>3 DEF NotificationsAt
<1> QED BY ONLY <1>4, <1>5 DEF EpochKnowledgeInvariant

THEOREM AdvertisePreservesEpochKnowledge ==
    ASSUME NEW c \in Replicas, NEW e, AdvertiseCommit(c, e),
           KnowledgeAt(knownCommitted, term', commitHistory'),
           NotificationsAt(commitMessages, commitHistory')
    PROVE EpochKnowledgeInvariant'
<1>1. KnownBy(commitHistory', term[c], e)
    BY SMT DEF AdvertiseCommit, KnowledgeAt
<1> QED BY SMT, <1>1 DEF AdvertiseCommit, EpochKnowledgeInvariant, KnowledgeAt, NotificationsAt

THEOREM LearnPreservesEpochKnowledge ==
    ASSUME KnowledgeShape, NEW r \in Replicas, NEW m, LearnCommit(r, m),
           KnowledgeAt(knownCommitted, term', commitHistory'),
           NotificationsAt(commitMessages, commitHistory')
    PROVE EpochKnowledgeInvariant'
<1>0. KnowledgeShape
    OBVIOUS
<1>1. KnownBy(commitHistory', term'[r], m.entry)
    BY SMT DEF LearnCommit, NotificationsAt
<1>2. knownCommitted' = [knownCommitted EXCEPT ![r] = @ \cup {m.entry}]
      /\ commitMessages' = commitMessages
    BY DEF LearnCommit
<1>3. KnowledgeAt(knownCommitted, term', commitHistory')
      /\ NotificationsAt(commitMessages, commitHistory')
    OBVIOUS
<1>4. KnowledgeAt(knownCommitted', term', commitHistory')
    BY ONLY KnowledgeAtInsertion, <1>0, <1>1, <1>2, <1>3 DEF KnowledgeShape
<1> QED BY ONLY <1>2, <1>3, <1>4 DEF EpochKnowledgeInvariant

THEOREM EpochKnowledgeInitially == Init => EpochKnowledgeInvariant
BY SMT DEF Init, EpochKnowledgeInvariant, KnowledgeAt, NotificationsAt

THEOREM EpochKnowledgeInductiveStep ==
    ASSUME ElectionInvariant, DurabilityInvariant, KnowledgeInvariant,
           EpochKnowledgeInvariant, CommitFaultsDisabled, Next
    PROVE EpochKnowledgeInvariant'
<1>1. ElectionInvariant' /\ ProtocolNext /\ Observe
      /\ ackMessages \subseteq ackMessages' /\ commitHistory \subseteq commitHistory'
    <2>1. ElectionInvariant'
        BY ElectionInductiveStep
    <2>2. ProtocolNext /\ Observe /\ DurableData
        BY DEF Next, DurabilityInvariant
    <2>3. DurabilityStep
        BY EveryStepPreservesDurabilityFacts, <2>2
    <2>4. commitHistory' = commitHistory \cup Evidence(ackMessages')
        BY <2>2 DEF Observe
    <2> QED BY ONLY SMT, <2>1, <2>2, <2>3, <2>4 DEF DurabilityStep
<1>2. term \in [Replicas -> Nat] /\ term' \in [Replicas -> Nat]
      /\ \A r \in Replicas : term[r] <= term'[r]
    BY SMT, <1>1, ElectionStepNeverDecreasesTerms DEF ElectionInvariant, ElectionTypes, Terms
<1>3. KnowledgeAt(knownCommitted, term', commitHistory')
      /\ NotificationsAt(commitMessages, commitHistory')
    BY EpochKnowledgeFrame, <1>1, <1>2
<1>4. KnowledgeChangingNext \/ UNCHANGED <<knownCommitted, commitMessages, confirmations>>
    BY ProtocolKnowledgeProjection, <1>1
<1> QED BY SMT, <1>1, <1>3, <1>4, CommitEntryPreservesEpochKnowledge,
    AdvertisePreservesEpochKnowledge, LearnPreservesEpochKnowledge
    DEF KnowledgeChangingNext, ConfirmProposal, EpochKnowledgeInvariant, KnowledgeInvariant, CommitFaultsDisabled

THEOREM EpochKnowledgeStuttering ==
    ASSUME EpochKnowledgeInvariant, UNCHANGED vars
    PROVE EpochKnowledgeInvariant'
BY SMT DEF EpochKnowledgeInvariant, vars, protocolVars, observerVars

THEOREM ProtocolEpochKnowledge == Spec => []EpochKnowledgeInvariant
<1>1. Spec => []ElectionInvariant /\ []DurabilityInvariant /\ []KnowledgeInvariant
    BY PTL, ElectionInvariantAlways, ProtocolAckDurability, ProtocolCommitKnowledge
<1>2. Init => EpochKnowledgeInvariant
    BY EpochKnowledgeInitially
<1>3. ElectionInvariant /\ DurabilityInvariant /\ KnowledgeInvariant /\ EpochKnowledgeInvariant
      /\ [Next]_vars => EpochKnowledgeInvariant'
    BY EpochKnowledgeInductiveStep, EpochKnowledgeStuttering DEF CommitFaultsDisabled
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
