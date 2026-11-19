-------------------------- MODULE TRaftAppendOnlyProof -----------------------
EXTENDS TRaftBoundaryCountFrames

LeaderLogGrowth == \A r \in Replicas :
    (role[r] = "Leader" /\ role'[r] = "Leader" /\ term[r] = term'[r]) => formal[r] \subseteq formal'[r]

THEOREM AddingOneEntryPreservesLeaderGrowth ==
    ASSUME formal \in [Replicas -> SUBSET Entries], NEW c \in Replicas, NEW e,
           formal' = [formal EXCEPT ![c] = formal[c] \cup {e}]
    PROVE LeaderLogGrowth
<1>1. \A r \in Replicas : formal[r] \subseteq formal'[r]
    <2>1. ASSUME NEW r \in Replicas
          PROVE formal[r] \subseteq formal'[r]
        <3>1. CASE r = c
            BY SMT, <3>1
        <3>2. CASE r # c
            BY SMT, <3>2
        <3> QED BY <3>1, <3>2
    <2> QED BY <2>1
<1> QED BY ONLY <1>1 DEF LeaderLogGrowth

THEOREM ConfirmKeepsExistingLeaders ==
    ASSUME formal \in [Replicas -> SUBSET Entries], NEW c \in Replicas, ConfirmProposal(c)
    PROVE LeaderLogGrowth
<1>0. formal \in [Replicas -> SUBSET Entries]
    OBVIOUS
<1>1. role[c] = "LeaderCandidate" /\
      formal' = [formal EXCEPT ![c] = Publish(c, current[c])]
    BY DEF ConfirmProposal
<1>2. ASSUME NEW r \in Replicas, role[r] = "Leader"
      PROVE formal[r] \subseteq formal'[r]
    <2>1. r # c
        BY ONLY SMT, <1>1, <1>2
    <2>2. formal'[r] = formal[r]
        BY ONLY SMT, <1>0, <1>1, <1>2, <2>1
    <2> QED BY ONLY <2>2
<1> QED BY ONLY <1>2 DEF LeaderLogGrowth

THEOREM LearnKeepsExistingLeaders ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
    PROVE LeaderLogGrowth
<1>1. role[r] = "Leader" => formal'[r] = formal[r]
    BY ExistingLeaderIgnoresOwnConfirmation
<1>2. \A s \in Replicas \ {r} : formal'[s] = formal[s]
    <2>0. formal \in [Replicas -> SUBSET Entries]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>1. formal' = [formal EXCEPT ![r] = Publish(r, p)]
        BY DEF LearnConfirmation
    <2> QED BY ONLY SMT, <2>0, <2>1
<1> QED BY ONLY SMT, <1>1, <1>2 DEF LeaderLogGrowth

THEOREM ExistingLeaderLogsGrow ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE LeaderLogGrowth
<1>0. formal \in [Replicas -> SUBSET Entries]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>1. BoundaryCountChanges \/ UNCHANGED <<formal, proposals>>
    BY BoundaryCountActionProjection
<1>2. \A c \in Replicas : \A p : BuildRecovery(c, p) => LeaderLogGrowth
    BY SMT DEF BuildRecovery, LeaderLogGrowth
<1>3. \A c \in Replicas : \A v : CreateEntry(c, v) => LeaderLogGrowth
    <2>1. ASSUME NEW c \in Replicas, NEW v, CreateEntry(c, v)
          PROVE LeaderLogGrowth
        <3>1. formal' = [formal EXCEPT ![c] = formal[c] \cup
                  {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]),
                         v, "data", Count(formal[c], Cur(formal[c]) - 1))}]
            BY <2>1 DEF CreateEntry
        <3> QED BY ONLY AddingOneEntryPreservesLeaderGrowth, <1>0, <2>1, <3>1
    <2> QED BY ONLY <2>1
<1>4. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) => LeaderLogGrowth
    <2>1. ASSUME NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
          PROVE LeaderLogGrowth
        <3>1. formal' = [formal EXCEPT ![c] = formal[c] \cup
                  {Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]) + 1,
                         v, k, Count(formal[c], Cur(formal[c])))}]
            BY <2>1 DEF CreateSuccessor
        <3> QED BY ONLY AddingOneEntryPreservesLeaderGrowth, <1>0, <2>1, <3>1
    <2> QED BY ONLY <2>1
<1>5. \A r \in Replicas : \A o : ReceiveEntry(r, o) => LeaderLogGrowth
    <2>1. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
          PROVE LeaderLogGrowth
        <3>1. formal' = [formal EXCEPT ![r] = formal[r] \cup {o.entry}]
            BY <2>1 DEF ReceiveEntry
        <3> QED BY ONLY AddingOneEntryPreservesLeaderGrowth, <1>0, <2>1, <3>1
    <2> QED BY ONLY <2>1
<1>6. \A c \in Replicas : ConfirmProposal(c) => LeaderLogGrowth
    BY ConfirmKeepsExistingLeaders, <1>0
<1>7. \A r \in Replicas : \A p : LearnConfirmation(r, p) => LeaderLogGrowth
    BY LearnKeepsExistingLeaders
<1>8. UNCHANGED <<formal, proposals>> => LeaderLogGrowth
    BY SMT DEF LeaderLogGrowth
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF BoundaryCountChanges

THEOREM LeaderAppendOnlyInductiveStep ==
    ASSUME ProofInvariant, LeaderAppendOnly, Next
    PROVE LeaderAppendOnly'
<1>1. LeaderLogGrowth
    BY ExistingLeaderLogsGrow DEF Next
<1>2. appendOnlyOK
    BY DEF LeaderAppendOnly
<1>3. appendOnlyOK' = (appendOnlyOK /\ LeaderLogGrowth)
    BY DEF Next, Observe, LeaderLogGrowth
<1> QED BY ONLY ZenonT(5), <1>1, <1>2, <1>3 DEF LeaderAppendOnly
=============================================================================
