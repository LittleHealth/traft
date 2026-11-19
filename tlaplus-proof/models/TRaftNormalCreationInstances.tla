---------------------- MODULE TRaftNormalCreationInstances -------------------
EXTENDS TRaftCanonicalUpdateProof
\* Expose the Boolean-specialized constructor to all backends.  Leaving a
\* state operator applied to TRUE/FALSE opaque obscures the literal entry.
USE DEF NormalCreatedEntry

THEOREM SuccessorCanonicalUpdate ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
    PROVE canonical' = [t \in Terms |-> IF t = term[c]
             THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, TRUE)} ELSE canonical[t]]
<1>1. LeaderData /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateHasLeaderData, CandidateCanonicalSources
<1>2. formal[c] = canonical[term[c]] /\ term[c] \in Terms /\ role[c] = "Leader"
      /\ formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, k, TRUE)}]
      /\ UNCHANGED <<role, term, proposals>>
    BY SMT DEF CreateEntry, CreateSuccessor, NormalCreatedEntry,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>3. DEFINE D == [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, TRUE)} ELSE canonical[t]]
<1>4. (\A t \in Terms : canonical[t] \subseteq D[t])
      /\ (\A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch])
      /\ (\A r \in Replicas : role'[r] = "Leader" =>
              term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]])
    BY SMT, <1>1, <1>2 DEF D, LeaderData
<1>5. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
    BY GhostUpperBound, <1>4
<1>6. NormalCreatedEntry(c, v, k, TRUE) \in canonical'[term[c]]
    BY SMT, <1>1, <1>2 DEF GhostNext, LeaderData
<1>7. \A t \in Terms : D[t] \subseteq canonical'[t]
    BY ONLY SMT, <1>5, <1>6 DEF D
<1>8. \A t \in Terms : canonical'[t] = D[t]
    BY ONLY ZenonT(5), <1>5, <1>7
<1> QED BY SMT, <1>8 DEF GhostNext, D


THEOREM OpenEntryCanonicalUpdate ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, CreateEntry(c, v)
    PROVE canonical' = [t \in Terms |-> IF t = term[c]
             THEN canonical[t] \cup {NormalCreatedEntry(c, v, "data", FALSE)} ELSE canonical[t]]
<1>1. LeaderData /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateHasLeaderData, CandidateCanonicalSources
<1>2. formal[c] = canonical[term[c]] /\ term[c] \in Terms /\ role[c] = "Leader"
      /\ formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, "data", FALSE)}]
      /\ UNCHANGED <<role, term, proposals>>
    BY SMT DEF CreateEntry, CreateSuccessor, NormalCreatedEntry,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>3. DEFINE D == [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, "data", FALSE)} ELSE canonical[t]]
<1>4. (\A t \in Terms : canonical[t] \subseteq D[t])
      /\ (\A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch])
      /\ (\A r \in Replicas : role'[r] = "Leader" =>
              term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]])
    BY SMT, <1>1, <1>2 DEF D, LeaderData
<1>5. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
    BY GhostUpperBound, <1>4
<1>6. NormalCreatedEntry(c, v, "data", FALSE) \in canonical'[term[c]]
    BY SMT, <1>1, <1>2 DEF GhostNext, LeaderData
<1>7. \A t \in Terms : D[t] \subseteq canonical'[t]
    BY ONLY SMT, <1>5, <1>6 DEF D
<1>8. \A t \in Terms : canonical'[t] = D[t]
    BY ONLY ZenonT(5), <1>5, <1>7
<1> QED BY SMT, <1>8 DEF GhostNext, D

=============================================================================
