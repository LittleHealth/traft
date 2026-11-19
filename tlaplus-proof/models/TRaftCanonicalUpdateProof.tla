---------------------- MODULE TRaftCanonicalUpdateProof ----------------------
EXTENDS TRaftCreatedEntryProof, TRaftCanonicalPrefixProof

THEOREM NoNewSourceKeepsCanonical ==
    ASSUME ProofInvariant, GhostNext, PostLeaderBound,
           term' \in [Replicas -> Terms], UNCHANGED proposals
    PROVE UNCHANGED canonical
<1>1. canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateCanonicalSources
<1>2. \A t \in Terms : canonical[t] \subseteq canonical[t]
    BY SMT
<1>3. \A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY <1>1
<1>4. \A r \in Replicas : role'[r] = "Leader" =>
          term'[r] \in Terms /\ formal'[r] \subseteq canonical[term'[r]]
    BY SMT DEF PostLeaderBound
<1>5. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq canonical[t]
    BY GhostUpperBound, <1>2, <1>3, <1>4
<1>6. \A t \in Terms : canonical'[t] = canonical[t]
    BY ONLY ZenonT(5), <1>5
<1> QED BY SMT, <1>1, <1>6 DEF GhostNext

THEOREM NormalAppendCanonicalUpdate ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
<1>1. LeaderData /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateHasLeaderData, CandidateCanonicalSources
<1>2. formal[c] = canonical[term[c]] /\ term[c] \in Terms /\ role[c] = "Leader"
      /\ formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, k, successor)}]
      /\ UNCHANGED <<role, term, proposals>>
    BY SMT DEF CreateEntry, CreateSuccessor, NormalCreatedEntry,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>3. DEFINE D == [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
<1>4. (\A t \in Terms : canonical[t] \subseteq D[t])
      /\ (\A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch])
      /\ (\A r \in Replicas : role'[r] = "Leader" =>
              term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]])
    BY SMT, <1>1, <1>2 DEF D, LeaderData
<1>5. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
    BY GhostUpperBound, <1>4
<1>6. NormalCreatedEntry(c, v, k, successor) \in canonical'[term[c]]
    BY SMT, <1>1, <1>2 DEF GhostNext, LeaderData
<1>7. \A t \in Terms : D[t] \subseteq canonical'[t]
    BY ONLY SMT, <1>5, <1>6 DEF D
<1>8. \A t \in Terms : canonical'[t] = D[t]
    BY ONLY ZenonT(5), <1>5, <1>7
<1> QED BY SMT, <1>8 DEF GhostNext, D

THEOREM RecoveryCanonicalUpdate ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
<1>1. canonical[term[c]] = {} /\ LeaderData
      /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY RecoveryCreationEpochIsEmpty, CandidateHasLeaderData, CandidateCanonicalSources
<1>2. proposals' = proposals \cup {CreatedRecoveryProposal(c, selected)}
      /\ CreatedRecoveryProposal(c, selected).epoch = term[c]
      /\ UNCHANGED <<term, role, formal>> /\ term[c] \in Terms
    BY SMT DEF BuildRecovery, CreatedRecoveryProposal, RecoveryCreatedEntry, Proposal,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>3. DEFINE D == [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
<1>4. (\A t \in Terms : canonical[t] \subseteq D[t])
      /\ (\A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch])
      /\ (\A r \in Replicas : role'[r] = "Leader" =>
              term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]])
    BY SMT, <1>1, <1>2 DEF D, LeaderData
<1>5. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
    BY GhostUpperBound, <1>4
<1>6. Result(CreatedRecoveryProposal(c, selected)) \subseteq canonical'[term[c]]
    BY SMT, <1>2 DEF GhostNext
<1>7. \A t \in Terms : D[t] \subseteq canonical'[t]
    BY ONLY SMT, <1>5, <1>6 DEF D
<1>8. \A t \in Terms : canonical'[t] = D[t]
    BY ONLY ZenonT(5), <1>5, <1>7
<1> QED BY SMT, <1>8 DEF GhostNext, D
=============================================================================
