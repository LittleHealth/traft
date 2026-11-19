-------------------- MODULE TRaftActivationCertificateProof ------------------
EXTENDS TRaftPrefixEvidenceState, TRaftCommitTemporal

THEOREM ConfirmationsOnlyGrow ==
    ASSUME ProtocolNext
    PROVE confirmations \subseteq confirmations'
<1>1. KnowledgeChangingNext \/ UNCHANGED <<knownCommitted, commitMessages, confirmations>>
    BY ProtocolKnowledgeProjection
<1> QED BY SMT, <1>1 DEF KnowledgeChangingNext, ConfirmProposal, CommitEntry, AdvertiseCommit, LearnCommit

THEOREM ActiveControlCertificateStep ==
    ASSUME ControlInvariant, ElectionInvariant, ActiveControlCertified, ProtocolNext
    PROVE ActiveControlCertified'
<1>0. ActiveControlCertified /\ role \in [Replicas -> Roles]
      /\ phase \in [Replicas -> Phases] /\ current \in [Replicas -> proposals \cup {NoProposal}]
    BY DEF ControlInvariant, ControlShape, ElectionInvariant, ElectionTypes
<1>1. ControlChangingNext \/ UNCHANGED ControlCoreVars
    BY ProtocolControlProjection
<1>2. confirmations \subseteq confirmations'
    BY ConfirmationsOnlyGrow
<1>3. \A c \in Replicas : StartElection(c) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF StartElection, ActiveControlCertified
<1>4. \A c \in Replicas : WinElection(c) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF WinElection, ActiveControlCertified
<1>5. \A c \in Replicas : ConfirmProposal(c) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF ConfirmProposal, ActiveControlCertified
<1>6. \A c \in Replicas : Activate(c) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF Activate, ActiveControlCertified
<1>7. \A c \in Replicas : Crash(c) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF Crash, ActiveControlCertified
<1>8. \A r \in Replicas, t \in Terms : AdoptTerm(r, t) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF AdoptTerm, ActiveControlCertified
<1>9. ASSUME NEW c \in Replicas, NEW p, BuildRecovery(c, p)
      PROVE ActiveControlCertified'
    <2>1. role' = role /\ role[c] = "LeaderCandidate"
          /\ phase' = [phase EXCEPT ![c] = "sync"]
          /\ \A r \in Replicas \ {c} : current'[r] = current[r]
        BY ONLY SMT, <1>0, <1>9 DEF BuildRecovery
    <2> QED BY ONLY SMT, <1>0, <1>2, <1>9, <2>1 DEF ActiveControlCertified
<1>10. (UNCHANGED <<role, phase, current>>) => ActiveControlCertified'
    BY ONLY SMT, <1>0, <1>2 DEF ActiveControlCertified
<1> QED BY ONLY ZenonT(10), <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10
    DEF ControlChangingNext, ControlCoreVars, MakeReport, DeliverReport

THEOREM LeaderViewsRetainRecoveryCertificate ==
    ASSUME LeaderViewsCertified, ActiveControlCertified', ControlInvariant',
           confirmations \subseteq confirmations', Observe
    PROVE LeaderViewsCertified'
<1>1. \A v \in leaderViews : \E p \in confirmations' : p.epoch = v.epoch
    BY SMT DEF LeaderViewsCertified
<1>2. \A r \in Replicas : role'[r] = "Leader" =>
          current'[r] \in confirmations' /\ current'[r].epoch = term'[r]
    BY SMT DEF ActiveControlCertified, ControlInvariant, ControlShape
<1> QED BY SMT, <1>1, <1>2 DEF LeaderViewsCertified, Observe

THEOREM ActiveRecoveryCertificatesInitially == Init => ActiveRecoveryCertificates
BY SMT DEF Init, ActiveRecoveryCertificates, ActiveControlCertified, LeaderViewsCertified

THEOREM ActiveRecoveryCertificatesStep ==
    ASSUME ControlInvariant, ElectionInvariant, ActiveRecoveryCertificates, Next
    PROVE ActiveRecoveryCertificates'
<1>1. ActiveControlCertified' /\ ControlInvariant' /\ confirmations \subseteq confirmations'
    BY ActiveControlCertificateStep, ControlInductiveStep, ConfirmationsOnlyGrow
       DEF ActiveRecoveryCertificates, Next
<1>2. LeaderViewsCertified'
    BY LeaderViewsRetainRecoveryCertificate, <1>1 DEF ActiveRecoveryCertificates, Next
<1> QED BY <1>1, <1>2 DEF ActiveRecoveryCertificates

THEOREM ActiveRecoveryCertificatesStuttering ==
    ASSUME ActiveRecoveryCertificates, UNCHANGED vars
    PROVE ActiveRecoveryCertificates'
BY SMT DEF ActiveRecoveryCertificates, ActiveControlCertified, LeaderViewsCertified,
   vars, protocolVars, observerVars

THEOREM ProtocolActiveRecoveryCertificates == Spec => []ActiveRecoveryCertificates
<1>1. Spec => []ControlInvariant /\ []ElectionInvariant
    BY PTL, ControlInvariantAlways, ElectionInvariantAlways
<1>2. Init => ActiveRecoveryCertificates
    BY ActiveRecoveryCertificatesInitially
<1>3. ControlInvariant /\ ElectionInvariant /\ ActiveRecoveryCertificates
      /\ [Next]_vars => ActiveRecoveryCertificates'
    BY ActiveRecoveryCertificatesStep, ActiveRecoveryCertificatesStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
