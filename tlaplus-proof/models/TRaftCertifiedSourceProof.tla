----------------------- MODULE TRaftCertifiedSourceProof ---------------------
EXTENDS TRaftCertifiedSourceState, TRaftBoundaryCountFrames,
        TRaftActivationCertificateProof, TRaftOfferProof

THEOREM CertifiedSourcesGrow ==
    ASSUME NEW V, NEW W, NEW P, NEW Q, V \subseteq W, P \subseteq Q
    PROVE CertifiedLogEntries(V, P) \subseteq CertifiedLogEntries(W, Q)
BY SMT DEF CertifiedLogEntries

THEOREM CertifiedSourceGrowthStep ==
    Next => CertifiedLogEntries(leaderViews, confirmations) \subseteq
                CertifiedLogEntries(leaderViews', confirmations')
<1>1. ASSUME Next
      PROVE CertifiedLogEntries(leaderViews, confirmations) \subseteq
                CertifiedLogEntries(leaderViews', confirmations')
    <2>1. leaderViews \subseteq leaderViews' /\ confirmations \subseteq confirmations'
        BY SMT, ConfirmationsOnlyGrow, <1>1 DEF Next, Observe
    <2> QED BY CertifiedSourcesGrow, <2>1
<1> QED BY <1>1

THEOREM ObservedLeaderHasCertifiedSource ==
    ASSUME NEW c \in Replicas, role'[c] = "Leader", Observe
    PROVE formal'[c] \subseteq CertifiedLogEntries(leaderViews', confirmations')
<1>1. [node |-> c, epoch |-> term'[c], entries |-> formal'[c]] \in leaderViews'
    BY SMT DEF Observe
<1> QED BY ONLY SMT, <1>1 DEF CertifiedLogEntries

THEOREM FormalSourceOneNodeUpdate ==
    ASSUME InstalledEntriesHaveSource,
           CertifiedLogEntries(leaderViews, confirmations) \subseteq CertifiedLogEntries(leaderViews', confirmations'),
           NEW r \in Replicas, formal'[r] \subseteq CertifiedLogEntries(leaderViews', confirmations'),
           \A s \in Replicas \ {r} : formal'[s] = formal[s]
    PROVE InstalledEntriesHaveSource'
BY SMT DEF InstalledEntriesHaveSource, FormalEntriesFrom

THEOREM NewLeaderEntriesHaveSource ==
    ASSUME InstalledEntriesHaveSource, FormalShape, NEW c \in Replicas, NEW v, NEW k,
           CreateEntry(c, v) \/ CreateSuccessor(c, v, k), Observe,
           CertifiedLogEntries(leaderViews, confirmations) \subseteq CertifiedLogEntries(leaderViews', confirmations')
    PROVE InstalledEntriesHaveSource'
<1>1. role'[c] = "Leader"
    BY SMT DEF CreateEntry, CreateSuccessor
<1>2. formal'[c] \subseteq CertifiedLogEntries(leaderViews', confirmations')
    BY ObservedLeaderHasCertifiedSource, <1>1
<1>3. \A s \in Replicas \ {c} : formal'[s] = formal[s]
    BY SMT DEF CreateEntry, CreateSuccessor, FormalShape
<1> QED BY FormalSourceOneNodeUpdate, <1>2, <1>3

THEOREM ReceivedEntryHasSource ==
    ASSUME InstalledEntriesHaveSource, FormalShape, OfferProvenance,
           NEW r \in Replicas, NEW o, ReceiveEntry(r, o),
           CertifiedLogEntries(leaderViews, confirmations) \subseteq CertifiedLogEntries(leaderViews', confirmations')
    PROVE InstalledEntriesHaveSource'
<1>1. PICK v \in leaderViews : o.entry \in v.entries
    BY SMT DEF ReceiveEntry, OfferProvenance
<1>2. o.entry \in CertifiedLogEntries(leaderViews', confirmations')
    BY SMT, <1>1 DEF CertifiedLogEntries
<1>3. formal'[r] \subseteq CertifiedLogEntries(leaderViews', confirmations')
      /\ \A s \in Replicas \ {r} : formal'[s] = formal[s]
    BY SMT, <1>2 DEF ReceiveEntry, FormalShape, InstalledEntriesHaveSource, FormalEntriesFrom
<1> QED BY FormalSourceOneNodeUpdate, <1>3

THEOREM PublishedRecoveryHasSource ==
    ASSUME InstalledEntriesHaveSource, FormalShape, NEW r \in Replicas, NEW p,
           formal' = [formal EXCEPT ![r] = Publish(r, p)], p \in confirmations',
           CertifiedLogEntries(leaderViews, confirmations) \subseteq CertifiedLogEntries(leaderViews', confirmations')
    PROVE InstalledEntriesHaveSource'
<1>1. Result(p) \subseteq CertifiedLogEntries(leaderViews', confirmations')
    BY SMT DEF CertifiedLogEntries
<1>2. formal'[r] \subseteq CertifiedLogEntries(leaderViews', confirmations')
      /\ \A s \in Replicas \ {r} : formal'[s] = formal[s]
    BY SMT, <1>1 DEF Publish, FormalShape, InstalledEntriesHaveSource, FormalEntriesFrom
<1> QED BY FormalSourceOneNodeUpdate, <1>2

THEOREM InstalledSourceInductiveStep ==
    ASSUME InstalledEntriesHaveSource, FormalShape, OfferProvenance, Next
    PROVE InstalledEntriesHaveSource'
<1>1. BoundaryCountChanges \/ UNCHANGED <<formal, proposals>>
    BY BoundaryCountActionProjection DEF Next
<1>2. CertifiedLogEntries(leaderViews, confirmations) \subseteq
            CertifiedLogEntries(leaderViews', confirmations') /\ confirmations \subseteq confirmations' /\ Observe
    BY CertifiedSourceGrowthStep, ConfirmationsOnlyGrow DEF Next
<1>3. \A c \in Replicas : \A p : BuildRecovery(c, p) => UNCHANGED formal
    BY SMT DEF BuildRecovery
<1>4. UNCHANGED formal => InstalledEntriesHaveSource'
    BY SMT, <1>2 DEF InstalledEntriesHaveSource, FormalEntriesFrom
<1>5. \A c \in Replicas : ConfirmProposal(c) => InstalledEntriesHaveSource'
    <2>1. ASSUME NEW c \in Replicas, ConfirmProposal(c)
          PROVE InstalledEntriesHaveSource'
        <3>1. formal' = [formal EXCEPT ![c] = Publish(c, current[c])]
              /\ current[c] \in confirmations' /\ c \in Replicas
            BY SMT, <2>1 DEF ConfirmProposal
        <3>2. InstalledEntriesHaveSource /\ FormalShape
              /\ CertifiedLogEntries(leaderViews, confirmations) \subseteq
                 CertifiedLogEntries(leaderViews', confirmations')
            BY <1>2
        <3> QED BY ONLY PublishedRecoveryHasSource, <3>1, <3>2
    <2> QED BY <2>1
<1>6. \A r \in Replicas : \A p : LearnConfirmation(r, p) => InstalledEntriesHaveSource'
    <2>1. ASSUME NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
          PROVE InstalledEntriesHaveSource'
        <3>1. formal' = [formal EXCEPT ![r] = Publish(r, p)]
              /\ p \in confirmations' /\ r \in Replicas
            BY SMT, <2>1 DEF LearnConfirmation
        <3>2. InstalledEntriesHaveSource /\ FormalShape
              /\ CertifiedLogEntries(leaderViews, confirmations) \subseteq
                 CertifiedLogEntries(leaderViews', confirmations')
            BY <1>2
        <3> QED BY ONLY PublishedRecoveryHasSource, <3>1, <3>2
    <2> QED BY <2>1
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6,
    NewLeaderEntriesHaveSource, ReceivedEntryHasSource DEF BoundaryCountChanges

THEOREM InstalledSourceInitially == Init => InstalledEntriesHaveSource
BY SMT DEF Init, InstalledEntriesHaveSource, FormalEntriesFrom

THEOREM InstalledSourceStuttering ==
    ASSUME InstalledEntriesHaveSource, UNCHANGED vars
    PROVE InstalledEntriesHaveSource'
BY SMT DEF InstalledEntriesHaveSource, FormalEntriesFrom, CertifiedLogEntries, vars, protocolVars, observerVars

THEOREM ProtocolInstalledSource == Spec => []InstalledEntriesHaveSource
<1>1. Spec => []FormalShape /\ []OfferProvenance
    BY PTL, ProtocolAckDurability, ProtocolOfferProvenance DEF DurabilityInvariant, DurableData
<1>2. Init => InstalledEntriesHaveSource
    BY InstalledSourceInitially
<1>3. FormalShape /\ OfferProvenance /\ InstalledEntriesHaveSource /\ [Next]_vars => InstalledEntriesHaveSource'
    BY InstalledSourceInductiveStep, InstalledSourceStuttering
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
