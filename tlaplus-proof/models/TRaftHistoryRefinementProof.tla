-------------------- MODULE TRaftHistoryRefinementProof ----------------------
EXTENDS TRaftProofState, TRaftProposalIdentityProof

LiveViews(R, T, F) == {[node |-> r, epoch |-> T[r], entries |-> F[r]] :
                          r \in {s \in Replicas : R[s] = "Leader"}}

\* canonical can be reconstructed from the already present proposal and
\* leader-view histories. This lifting adds no enabling condition to Next.
LiftedInit(C) == Init /\ C = [t \in Terms |-> {}]
LiftedNext(C) == Next /\ C' = [t \in Terms |-> C[t] \cup
    ProposedAt(proposals', t) \cup
    (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})]
LiftedVars(C) == <<vars, C>>
LiftedSpec(C) == LiftedInit(C) /\ [][LiftedNext(C)]_<<vars, C>>

THEOREM HistoryTemplateIdentity == ProofSpec <=> LiftedSpec(canonical)
BY DEF ProofSpec, ProofInit, ProofNext, GhostInit, GhostNext, proofVars,
       LiftedSpec, LiftedInit, LiftedNext, LiftedVars, ProposedAt

THEOREM ProposedAtMonotone ==
    ASSUME NEW P, NEW Q, P \subseteq Q, NEW t
    PROVE ProposedAt(P, t) \subseteq ProposedAt(Q, t)
BY SMT DEF ProposedAt

THEOREM ViewedAtUnion ==
    ASSUME NEW V, NEW W, NEW t
    PROVE ViewedAt(V \cup W, t) = ViewedAt(V, t) \cup ViewedAt(W, t)
BY SMT DEF ViewedAt

THEOREM LiveViewContents ==
    ASSUME NEW R, NEW T, NEW F, NEW t
    PROVE ViewedAt(LiveViews(R, T, F), t) =
            (UNION {F[r] : r \in {s \in Replicas : R[s] = "Leader" /\ T[s] = t}})
<1>1. ASSUME NEW x \in ViewedAt(LiveViews(R, T, F), t)
      PROVE x \in (UNION {F[r] : r \in {s \in Replicas : R[s] = "Leader" /\ T[s] = t}})
    <2>1. PICK v \in LiveViews(R, T, F) : v.epoch = t /\ x \in v.entries
        BY ONLY ZenonT(10), <1>1 DEF ViewedAt
    <2>2. PICK r \in Replicas : R[r] = "Leader" /\
                 v = [node |-> r, epoch |-> T[r], entries |-> F[r]]
        BY ONLY ZenonT(10), <2>1 DEF LiveViews
    <2> QED BY ONLY SMT, <2>1, <2>2
<1>2. ASSUME NEW x \in (UNION {F[r] : r \in {s \in Replicas : R[s] = "Leader" /\ T[s] = t}})
      PROVE x \in ViewedAt(LiveViews(R, T, F), t)
    <2>1. PICK r \in Replicas : R[r] = "Leader" /\ T[r] = t /\ x \in F[r]
        BY ONLY ZenonT(10), <1>2
    <2>2. [node |-> r, epoch |-> T[r], entries |-> F[r]] \in LiveViews(R, T, F)
        BY ONLY SMT, <2>1 DEF LiveViews
    <2> QED BY ONLY SMT, <2>1, <2>2 DEF ViewedAt
<1> QED BY ONLY ZenonT(10), <1>1, <1>2

THEOREM ProposalsNeverShrink == ProtocolNext => proposals \subseteq proposals'
<1>1. \A c, p : BuildRecovery(c, p) => proposals \subseteq proposals'
    BY ZenonT(10) DEF BuildRecovery
<1> QED BY SMT, <1>1, OnlyRecoveryCreatesProposal

THEOREM DerivedCanonicalFollowsObserver ==
    ASSUME proposals \subseteq proposals', Observe
    PROVE DerivedCanonical' = [t \in Terms |-> DerivedCanonical[t] \cup
              ProposedAt(proposals', t) \cup
              (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})]
<1>1. \A t \in Terms : ProposedAt(proposals, t) \subseteq ProposedAt(proposals', t)
    BY SMT, ProposedAtMonotone
<1>2. leaderViews' = leaderViews \cup LiveViews(role', term', formal')
    BY DEF Observe, LiveViews
<1>3. \A t \in Terms : ViewedAt(leaderViews', t) = ViewedAt(leaderViews, t) \cup
       (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
    <2>1. ASSUME NEW t \in Terms
          PROVE ViewedAt(leaderViews', t) = ViewedAt(leaderViews, t) \cup
                (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
        <3>1. ViewedAt(leaderViews', t) = ViewedAt(leaderViews, t) \cup
                  ViewedAt(LiveViews(role', term', formal'), t)
            BY ONLY SMT, <1>2, ViewedAtUnion
        <3>2. ViewedAt(LiveViews(role', term', formal'), t) =
                  (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
            BY LiveViewContents
        <3> QED BY <3>1, <3>2
    <2> QED BY <2>1
<1>4. \A t \in Terms : DerivedCanonical'[t] = DerivedCanonical[t] \cup
              ProposedAt(proposals', t) \cup
              (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
    <2>1. ASSUME NEW t \in Terms
          PROVE DerivedCanonical'[t] = DerivedCanonical[t] \cup
              ProposedAt(proposals', t) \cup
              (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
        <3>1. ProposedAt(proposals, t) \subseteq ProposedAt(proposals', t)
            BY <1>1
        <3>2. ViewedAt(leaderViews', t) = ViewedAt(leaderViews, t) \cup
              (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
            BY <1>3
        <3> QED BY ONLY SMT, <2>1, <3>1, <3>2 DEF DerivedCanonical
    <2> QED BY <2>1
<1>5. DerivedCanonical' = [t \in Terms |->
          ProposedAt(proposals', t) \cup ViewedAt(leaderViews', t)]
    BY ONLY SMT DEF DerivedCanonical
<1> QED BY ONLY SMT, <1>4, <1>5

THEOREM CoreInitializationLifts == Init => LiftedInit(DerivedCanonical)
<1>0. SUFFICES ASSUME Init PROVE LiftedInit(DerivedCanonical)
    OBVIOUS
<1>1. proposals = {} /\ leaderViews = {}
    BY <1>0 DEF Init
<1>2. \A t \in Terms : ProposedAt(proposals, t) = {} /\ ViewedAt(leaderViews, t) = {}
    BY ONLY SMT, <1>1 DEF ProposedAt, ViewedAt
<1>3. DerivedCanonical = [t \in Terms |-> {}]
    BY ONLY IsaM("auto"), <1>2 DEF DerivedCanonical
<1> QED BY <1>0, <1>3 DEF LiftedInit

THEOREM CoreNextLifts == Next => LiftedNext(DerivedCanonical)
<1>0. SUFFICES ASSUME Next PROVE LiftedNext(DerivedCanonical)
    OBVIOUS
<1>1. proposals \subseteq proposals' /\ Observe
    BY SMT, <1>0, ProposalsNeverShrink DEF Next
<1> QED BY DerivedCanonicalFollowsObserver, <1>0, <1>1 DEF LiftedNext

THEOREM CoreStutteringLifts == UNCHANGED vars => UNCHANGED LiftedVars(DerivedCanonical)
BY SMT DEF LiftedVars, DerivedCanonical, vars, protocolVars, observerVars

THEOREM CoreAndHistoryRefinement == Spec => LiftedSpec(DerivedCanonical)
<1>1. Init => LiftedInit(DerivedCanonical)
    BY CoreInitializationLifts
<1>2. [Next]_vars => [LiftedNext(DerivedCanonical)]_<<vars, DerivedCanonical>>
    BY SMT, CoreNextLifts, CoreStutteringLifts DEF LiftedVars
<1> QED BY PTL, <1>1, <1>2 DEF Spec, LiftedSpec
=============================================================================
