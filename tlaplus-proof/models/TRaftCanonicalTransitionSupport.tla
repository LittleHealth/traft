------------------- MODULE TRaftCanonicalTransitionSupport -------------------
EXTENDS TRaftBoundaryCountSupport, TRaftProposalIdentityProof
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM CandidateEpochHasNoPastLeaderView ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas,
           role[c] = "LeaderCandidate"
    PROVE ~\E v \in leaderViews : v.epoch = term[c]
<1>0. ElectionSafety
    OBVIOUS
<1>1. [node |-> c, epoch |-> term[c]] \in winners
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, ElectionInvariant, ElectionWinnerFacts
<1>2. ASSUME NEW v \in leaderViews, v.epoch = term[c]
      PROVE FALSE
    <2>1. [node |-> v.node, epoch |-> v.epoch] \in winners
        BY <1>2 DEF ProofInvariant, LeaderHistoryInvariant, LeaderViewCertificates
    <2>2. v.node = c
        BY ONLY SMT, <1>0, <1>1, <1>2, <2>1 DEF ElectionSafety
    <2>3. role[c] \in {"Leader", "Follower"}
        BY SMT, <1>2, <2>2 DEF ProofInvariant, LeaderHistoryInvariant, PastLeaderViews
    <2> QED BY SMT, <2>3
<1> QED BY <1>2

THEOREM CandidateCanonicalIsRecoveryResult ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas,
           role[c] = "LeaderCandidate", NEW p \in proposals, p.epoch = term[c]
    PROVE canonical[term[c]] = Result(p)
<1>1. ~\E v \in leaderViews : v.epoch = term[c]
    BY CandidateEpochHasNoPastLeaderView
<1>2. ViewedAt(leaderViews, term[c]) = {}
    BY ONLY SMT, <1>1 DEF ViewedAt
<1>3. \A q \in proposals : q.epoch = term[c] => q = p
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>4. p \in proposals /\ p.epoch = term[c]
    OBVIOUS
<1>5. ProposedAt(proposals, term[c]) = Result(p)
    BY ONLY SMT, <1>3, <1>4 DEF ProposedAt
<1>6. term[c] \in Terms /\ canonical = DerivedCanonical
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalDefinition
<1>7. canonical[term[c]] = ProposedAt(proposals, term[c]) \cup ViewedAt(leaderViews, term[c])
    BY ONLY SMT, <1>6 DEF DerivedCanonical
<1> QED BY ONLY ZenonT(5), <1>2, <1>5, <1>7

THEOREM CurrentTermEntryPinsSublogEpoch ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW e \in formal[r], e.term = term[r]
    PROVE LastTerm(formal[r]) = term[r] /\ formal[r] \subseteq canonical[term[r]]
<1>1. formal[r] # {} /\ formal[r] \subseteq Entries /\ IsFiniteSet(formal[r])
      /\ term[r] \in Nat
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, FiniteLogInvariant, FiniteNodeData, Terms
<1>2. PICK lastEntry \in formal[r] : lastEntry.term = LastTerm(formal[r])
    BY NonemptyLogLastTermIsRepresented, <1>1
<1>30. \A x \in formal[r] : x.term \in Nat /\ x.term <= term[r]
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       CanonicalShape, TypeOK, Entries, Terms
<1>3. LastTerm(formal[r]) \in Nat /\ LastTerm(formal[r]) <= term[r]
    BY ONLY SMT, <1>2, <1>30
<1>4. LastTerm(formal[r]) \in Terms /\ formal[r] \subseteq canonical[LastTerm(formal[r])]
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       CanonicalShape, Sublog
<1>50. \A t \in Terms : \A x \in canonical[t] : x.term <= t
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>51. e \in formal[r] /\ e.term = term[r]
    OBVIOUS
<1>5. term[r] <= LastTerm(formal[r])
    BY ONLY SMT, <1>4, <1>50, <1>51
<1> QED BY SMT, <1>1, <1>3, <1>4, <1>5

THEOREM ActivationAlreadyHasFullCanonicalLog ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, Activate(c)
    PROVE formal[c] = canonical[term[c]]
<1>1. current[c] \in proposals /\ current[c].epoch = term[c]
      /\ role[c] = "LeaderCandidate" /\ Result(current[c]) \subseteq formal[c]
    BY SMT DEF Activate, ProofInvariant, PreProvenanceInvariant, ControlInvariant, ControlShape
<1>20. \A p \in proposals : p.first.term = p.epoch
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. current[c].first \in formal[c] /\ current[c].first.term = term[c]
    BY ONLY SMT, <1>1, <1>20 DEF Result
<1>3. formal[c] \subseteq canonical[term[c]]
    BY CurrentTermEntryPinsSublogEpoch, <1>2
<1>4. canonical[term[c]] = Result(current[c])
    BY CandidateCanonicalIsRecoveryResult, <1>1
<1> QED BY ONLY SMT, <1>1, <1>3, <1>4

THEOREM RecoveryCreationEpochIsEmpty ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, NEW p, BuildRecovery(c, p)
    PROVE canonical[term[c]] = {}
<1>1. phase[c] = "collect" /\ role[c] = "LeaderCandidate"
      /\ ControlInvariant /\ ElectionInvariant
    BY DEF BuildRecovery, ProofInvariant, PreProvenanceInvariant
<1>2. [node |-> c, epoch |-> term[c]] \in winners
    BY SMT, <1>1 DEF ElectionInvariant, ElectionWinnerFacts
<1>3. ~\E q \in proposals : q.epoch = term[c]
    BY RecoveryCreatorHasFreshEpoch, <1>1, <1>2
<1>4. term[c] \in Terms
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>5. \A t \in Terms : canonical[t] # {} => \E q \in proposals : q.epoch = t
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1> QED BY ONLY ZenonT(5), <1>3, <1>4, <1>5
=============================================================================
