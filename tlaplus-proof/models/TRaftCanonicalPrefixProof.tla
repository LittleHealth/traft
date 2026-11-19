----------------------- MODULE TRaftCanonicalPrefixProof ---------------------
EXTENDS TRaftCanonicalLeaderFrames

CanonicalPrefixesPersist(C, D) == \A t \in Terms : \A e \in C[t] :
    Prefix(D[t], e.part - 1) = Prefix(C[t], e.part - 1)

THEOREM CandidateCanonicalSources == ProofInvariant =>
    /\ canonical \in [Terms -> SUBSET Entries]
    /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape

THEOREM GhostUpperBound ==
    ASSUME NEW D, GhostNext, \A t \in Terms : canonical[t] \subseteq D[t],
           \A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch],
           \A r \in Replicas : role'[r] = "Leader" =>
               term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]]
    PROVE \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
BY SMT DEF GhostNext

THEOREM ConstantCanonicalSourcesKeepPrefixes ==
    ASSUME ProofInvariant, GhostNext, PostLeaderBound,
           term' \in [Replicas -> Terms], UNCHANGED proposals
    PROVE CanonicalPrefixesPersist(canonical, canonical')
<1>1. canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateCanonicalSources
<1>10. PostLeaderBound /\ term' \in [Replicas -> Terms] /\ UNCHANGED proposals /\ GhostNext
    OBVIOUS
<1>11. \A t \in Terms : canonical[t] \subseteq canonical[t]
    BY SMT
<1>12. \A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY ONLY <1>1, <1>10
<1>13. \A r \in Replicas : role'[r] = "Leader" =>
           term'[r] \in Terms /\ formal'[r] \subseteq canonical[term'[r]]
    BY ONLY SMT, <1>10 DEF PostLeaderBound
<1>14. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq canonical[t]
    BY ONLY GhostUpperBound, <1>10, <1>11, <1>12, <1>13
<1>2. \A t \in Terms : canonical'[t] = canonical[t]
    BY ONLY ZenonT(5), <1>14
<1> QED BY ONLY SMT, <1>2 DEF CanonicalPrefixesPersist

THEOREM BuildRecoveryKeepsCanonicalPrefixes ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE CanonicalPrefixesPersist(canonical, canonical')
<1>1. canonical[term[c]] = {} /\ LeaderData
      /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY RecoveryCreationEpochIsEmpty, CandidateHasLeaderData, CandidateCanonicalSources
<1>2. UNCHANGED <<term, role, formal>>
      /\ \A p \in proposals' \ proposals : p.epoch = term[c]
    BY SMT DEF BuildRecovery, Proposal
<1>3. \A t \in Terms \ {term[c]} : canonical'[t] = canonical[t]
    <2>1. ASSUME NEW t \in Terms \ {term[c]}
          PROVE canonical'[t] = canonical[t]
        <3>1. \A p \in proposals' : p.epoch = t =>
                  p \in proposals /\ Result(p) \subseteq canonical[t]
            BY ONLY SMT, <1>1, <1>2, <2>1
        <3>2. \A r \in Replicas : role'[r] = "Leader" /\ term'[r] = t =>
                  formal'[r] \subseteq canonical[t]
            BY ONLY SMT, <1>1, <1>2 DEF LeaderData
        <3>3. canonical'[t] = canonical[t] \cup
                  (UNION {Result(p) : p \in {q \in proposals' : q.epoch = t}}) \cup
                  (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
            BY <2>1 DEF GhostNext
        <3>4. (UNION {Result(p) : p \in {q \in proposals' : q.epoch = t}}) \subseteq canonical[t]
            BY ONLY ZenonT(5), <3>1
        <3>5. (UNION {formal'[r] : r \in {s \in Replicas : role'[s] = "Leader" /\ term'[s] = t}})
                  \subseteq canonical[t]
            BY ONLY ZenonT(5), <3>2
        <3> QED BY ONLY IsaM("auto"), <3>3, <3>4, <3>5
    <2> QED BY <2>1
<1> QED BY ONLY SMT, <1>1, <1>3 DEF CanonicalPrefixesPersist

THEOREM SingleAppendKeepsCanonicalPrefixes ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW e,
           formal' = [formal EXCEPT ![c] = formal[c] \cup {e}],
           UNCHANGED <<role, term, proposals>>,
           formal[c] = canonical[term[c]],
           e.part \in Int, \A x \in formal[c] : x.part \in Int /\ x.part <= e.part
    PROVE CanonicalPrefixesPersist(canonical, canonical')
<1>1. LeaderData /\ canonical \in [Terms -> SUBSET Entries]
      /\ \A p \in proposals : p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
    BY CandidateHasLeaderData, CandidateCanonicalSources
<1>2. DEFINE D == [t \in Terms |-> IF t = term[c] THEN canonical[t] \cup {e} ELSE canonical[t]]
<1>3. (\A t \in Terms : canonical[t] \subseteq D[t])
      /\ (\A p \in proposals' : p.epoch \in Terms /\ Result(p) \subseteq D[p.epoch])
      /\ (\A r \in Replicas : role'[r] = "Leader" =>
              term'[r] \in Terms /\ formal'[r] \subseteq D[term'[r]])
    BY SMT, <1>1 DEF D, LeaderData
<1>4. \A t \in Terms : canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq D[t]
    BY GhostUpperBound, <1>3
<1>5. ASSUME NEW t \in Terms, NEW x \in canonical[t]
      PROVE Prefix(canonical'[t], x.part - 1) = Prefix(canonical[t], x.part - 1)
    <2>1. CASE t # term[c]
        <3>0. t \in Terms /\ t # term[c]
            BY <1>5, <2>1
        <3>1. D[t] = canonical[t]
            BY ONLY SMT, <3>0 DEF D
        <3>2. canonical[t] \subseteq canonical'[t] /\ canonical'[t] \subseteq canonical[t]
            BY ONLY <1>4, <3>0, <3>1
        <3>3. canonical'[t] = canonical[t]
            BY ONLY ZenonT(5), <3>2
        <3> QED BY <3>3
    <2>2. CASE t = term[c]
        <3>1. x.part \in Int /\ e.part \in Int /\ x.part <= e.part
            BY SMT, <1>5, <2>2
        <3> QED BY SMT, <1>4, <1>5, <2>2, <3>1 DEF D, Prefix
    <2> QED BY <2>1, <2>2
<1> QED BY <1>5 DEF CanonicalPrefixesPersist

THEOREM NormalCreationKeepsCanonicalPrefixes ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, NEW k,
           CreateEntry(c, v) \/ CreateSuccessor(c, v, k)
    PROVE CanonicalPrefixesPersist(canonical, canonical')
<1>1. formal[c] \subseteq Entries /\ IsFiniteSet(formal[c])
      /\ (role[c] = "Leader" => formal[c] = canonical[term[c]])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
       CanonicalShape, FiniteLogInvariant, FiniteNodeData
<1>2. Cur(formal[c]) \in Int /\ \A x \in formal[c] : x.part \in Int /\ x.part <= Cur(formal[c])
    BY FiniteLogPartitionFrontier, <1>1
<1>3. CASE CreateEntry(c, v)
    <2>1. DEFINE e == Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]), v, "data",
                             Count(formal[c], Cur(formal[c]) - 1))
    <2>2. formal' = [formal EXCEPT ![c] = formal[c] \cup {e}]
          /\ UNCHANGED <<role, term, proposals>> /\ formal[c] = canonical[term[c]]
          /\ e.part \in Int /\ \A x \in formal[c] : x.part \in Int /\ x.part <= e.part
        BY SMT, <1>1, <1>2, <1>3 DEF CreateEntry, e, Entry
    <2> QED BY SingleAppendKeepsCanonicalPrefixes, <2>2
<1>4. CASE CreateSuccessor(c, v, k)
    <2>1. DEFINE e == Entry(LastIndex(formal[c]) + 1, term[c], Cur(formal[c]) + 1, v, k,
                             Count(formal[c], Cur(formal[c])))
    <2>2. formal' = [formal EXCEPT ![c] = formal[c] \cup {e}]
          /\ UNCHANGED <<role, term, proposals>> /\ formal[c] = canonical[term[c]]
          /\ e.part \in Int /\ \A x \in formal[c] : x.part \in Int /\ x.part <= e.part
        BY SMT, <1>1, <1>2, <1>4 DEF CreateSuccessor, e, Entry
    <2> QED BY SingleAppendKeepsCanonicalPrefixes, <2>2
<1> QED BY <1>3, <1>4

THEOREM CanonicalPrefixesInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ProofNext, term' \in [Replicas -> Terms]
    PROVE CanonicalPrefixesPersist(canonical, canonical')
<1>1. ProtocolNext /\ GhostNext
    BY DEF ProofNext, Next
<1>2. NormalCreation \/ PostLeaderBound
    BY OnlyNormalCreationExtendsLeaderCanonical, <1>1
<1>3. (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
          \/ UNCHANGED proposals
    BY OnlyRecoveryCreatesProposal, <1>1
<1> QED BY SMT, <1>1, <1>2, <1>3, ConstantCanonicalSourcesKeepPrefixes,
    BuildRecoveryKeepsCanonicalPrefixes, NormalCreationKeepsCanonicalPrefixes DEF NormalCreation
=============================================================================
