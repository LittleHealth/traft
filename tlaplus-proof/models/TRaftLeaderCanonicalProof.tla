------------------------ MODULE TRaftLeaderCanonicalProof --------------------
EXTENDS TRaftLeaderCanonicalInclusion

PostLeaderEqualsCanonical == \A r \in Replicas :
    role'[r] = "Leader" => formal'[r] = canonical'[term'[r]]

THEOREM CurrentEpochOwnersAreUnique ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, NEW r \in Replicas,
           role[c] \in {"LeaderCandidate", "Leader"}, role[r] = "Leader", term[c] = term[r]
    PROVE c = r
<1>1. [node |-> c, epoch |-> term[c]] \in winners
      /\ [node |-> r, epoch |-> term[r]] \in winners
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, ElectionInvariant, ElectionWinnerFacts
<1> QED BY SMT, <1>1 DEF ElectionSafety

THEOREM CandidateEpochHasNoActiveLeader ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, role[c] = "LeaderCandidate"
    PROVE \A r \in Replicas : role[r] = "Leader" => term[r] # term[c]
BY SMT, CurrentEpochOwnersAreUnique

THEOREM NormalCreationKeepsLeaderEquality ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE PostLeaderEqualsCanonical
<1>1. formal \in [Replicas -> SUBSET Entries] /\ term \in [Replicas -> Terms]
      /\ (\A r \in Replicas : role[r] = "Leader" => formal[r] = canonical[term[r]])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>2. role[c] = "Leader" /\ UNCHANGED <<role, term>>
      /\ formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, k, successor)}]
    BY SMT DEF CreateEntry, CreateSuccessor, NormalCreatedEntry
<1>3. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
    BY NormalAppendCanonicalUpdate
<1>4. \A r \in Replicas : role[r] = "Leader" /\ term[r] = term[c] => r = c
    BY CurrentEpochOwnersAreUnique, <1>2
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4 DEF PostLeaderEqualsCanonical

THEOREM RecoveryCreationKeepsLeaderEquality ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE PostLeaderEqualsCanonical
<1>1. term \in [Replicas -> Terms]
      /\ (\A r \in Replicas : role[r] = "Leader" => formal[r] = canonical[term[r]])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>2. role[c] = "LeaderCandidate" /\ UNCHANGED <<formal, role, term>>
    BY DEF BuildRecovery
<1>3. \A r \in Replicas : role[r] = "Leader" => term[r] # term[c]
    BY CandidateEpochHasNoActiveLeader, <1>2
<1>4. canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4 DEF PostLeaderEqualsCanonical

THEOREM LeaderCanonicalEqualityInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ProofNext, term' \in [Replicas -> Terms]
    PROVE PostLeaderEqualsCanonical
<1>1. ProtocolNext /\ GhostNext
    BY DEF ProofNext, Next
<1>2. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryCreationKeepsLeaderEquality, <1>1, <1>2
<1>3. CASE NormalCreation
    BY NormalCreationKeepsLeaderEquality, <1>1, <1>3 DEF NormalCreation
<1>4. CASE ~NormalCreation /\ ~\E c \in Replicas : \E selected : BuildRecovery(c, selected)
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyNormalCreationExtendsLeaderCanonical, OnlyRecoveryCreatesProposal, <1>1, <1>4
    <2>2. UNCHANGED canonical /\ PostLeaderIncludesOldCanonical
        BY NoNewSourceKeepsCanonical, PostLeadersContainOldCanonical, <1>1, <2>1
    <2> QED BY ONLY ZenonT(5), <2>1, <2>2 DEF PostLeaderEqualsCanonical, PostLeaderBound, PostLeaderIncludesOldCanonical
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
