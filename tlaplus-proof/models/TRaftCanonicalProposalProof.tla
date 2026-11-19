---------------------- MODULE TRaftCanonicalProposalProof --------------------
EXTENDS TRaftCanonicalUpdateProof

ProposalCanonicalLinks(C, P) == \A p \in P :
    /\ p.epoch \in Terms /\ Result(p) \subseteq C[p.epoch]
    /\ Prefix(C[p.epoch], p.first.part - 1) = p.prefix
    /\ \A e \in C[p.epoch] \ Result(p) :
          e.term = p.epoch /\ e.index > p.first.index /\ e.part >= p.first.part

THEOREM CandidateProposalCanonicalLinks == ProofInvariant => ProposalCanonicalLinks(canonical, proposals)
BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape, ProposalCanonicalLinks

THEOREM NormalCreationKeepsProposalLinks ==
    ASSUME ProofInvariant, GhostNext, NEW c \in Replicas, NEW v, NEW k, NEW successor \in BOOLEAN,
           IF successor THEN CreateSuccessor(c, v, k) ELSE (CreateEntry(c, v) /\ k = "data")
    PROVE ProposalCanonicalLinks(canonical', proposals')
<1>1. ProposalCanonicalLinks(canonical, proposals)
      /\ formal[c] = canonical[term[c]] /\ IsFiniteSet(formal[c]) /\ formal[c] \subseteq Entries
      /\ term[c] \in Terms /\ UNCHANGED proposals
    BY CandidateProposalCanonicalLinks DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, CanonicalShape, FiniteLogInvariant, FiniteNodeData, CreateEntry, CreateSuccessor
<1>2. canonical' = [t \in Terms |-> IF t = term[c]
                THEN canonical[t] \cup {NormalCreatedEntry(c, v, k, successor)} ELSE canonical[t]]
    BY NormalAppendCanonicalUpdate
<1>30. CreateEntry(c, v) \/ CreateSuccessor(c, v, k)
    BY SMT
<1>3. CanonicalPrefixesPersist(canonical, canonical')
    BY NormalCreationKeepsCanonicalPrefixes, <1>30
<1>4. Cur(formal[c]) \in Int /\ \A x \in formal[c] : x.part \in Int /\ x.part <= Cur(formal[c])
    BY FiniteLogPartitionFrontier, <1>1
<1>5. LastIndex(formal[c]) \in Nat
      /\ \A x \in formal[c] : x.index \in Nat /\ x.index <= LastIndex(formal[c])
    BY FiniteLogNumericFrontier, <1>1
<1>6. ASSUME NEW p \in proposals
      PROVE /\ Result(p) \subseteq canonical'[p.epoch]
            /\ Prefix(canonical'[p.epoch], p.first.part - 1) = p.prefix
            /\ \A e \in canonical'[p.epoch] \ Result(p) :
                  e.term = p.epoch /\ e.index > p.first.index /\ e.part >= p.first.part
    <2>1. p.epoch \in Terms /\ Result(p) \subseteq canonical[p.epoch]
          /\ p.first \in canonical[p.epoch]
          /\ Prefix(canonical[p.epoch], p.first.part - 1) = p.prefix
        BY SMT, <1>1, <1>6 DEF ProposalCanonicalLinks, Result
    <2>2. Prefix(canonical'[p.epoch], p.first.part - 1) = p.prefix
        BY <1>3, <2>1 DEF CanonicalPrefixesPersist
    <2>3. CASE p.epoch # term[c]
        BY SMT, <1>1, <1>2, <1>6, <2>1, <2>2, <2>3 DEF ProposalCanonicalLinks
    <2>4. CASE p.epoch = term[c]
        <3>1. p.first \in formal[c]
            BY <1>1, <2>1, <2>4
        <3>2. NormalCreatedEntry(c, v, k, successor).term = p.epoch
              /\ NormalCreatedEntry(c, v, k, successor).index > p.first.index
              /\ NormalCreatedEntry(c, v, k, successor).part >= p.first.part
            BY ONLY SMT, <1>4, <1>5, <2>4, <3>1 DEF NormalCreatedEntry, Entry
        <3> QED BY SMT, <1>1, <1>2, <1>6, <2>1, <2>2, <2>4, <3>2 DEF ProposalCanonicalLinks
    <2> QED BY <2>3, <2>4
<1> QED BY SMT, <1>1, <1>6 DEF ProposalCanonicalLinks

THEOREM RecoveryKeepsProposalLinks ==
    ASSUME ProofInvariant, ElectionSafety, GhostNext,
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE ProposalCanonicalLinks(canonical', proposals')
<1>1. ProposalCanonicalLinks(canonical, proposals) /\ canonical[term[c]] = {}
      /\ term[c] \in Terms
    BY CandidateProposalCanonicalLinks, RecoveryCreationEpochIsEmpty
       DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. \A p \in proposals : p.epoch # term[c]
    BY SMT, <1>1 DEF ProposalCanonicalLinks, Result
<1>3. canonical' = [t \in Terms |-> IF t = term[c]
                THEN Result(CreatedRecoveryProposal(c, selected)) ELSE canonical[t]]
    BY RecoveryCanonicalUpdate
<1>4. proposals' = proposals \cup {CreatedRecoveryProposal(c, selected)}
    BY DEF BuildRecovery, CreatedRecoveryProposal, RecoveryCreatedEntry
<1>5. Recovered(c, selected) \subseteq Entries /\ IsFiniteSet(Recovered(c, selected))
    BY RecoveryInputIsFiniteTypedAndCoherent
<1>6. Cur(Recovered(c, selected)) \in Int
      /\ \A x \in Recovered(c, selected) : x.part \in Int /\ x.part <= Cur(Recovered(c, selected))
    BY FiniteLogPartitionFrontier, <1>5
<1>7. Prefix(Result(CreatedRecoveryProposal(c, selected)),
             RecoveryCreatedEntry(c, selected).part - 1) = Recovered(c, selected)
    BY ONLY SMT, <1>6 DEF CreatedRecoveryProposal, RecoveryCreatedEntry, Proposal, Entry, Result, Prefix
<1>8. CreatedRecoveryProposal(c, selected).epoch = term[c]
      /\ CreatedRecoveryProposal(c, selected).prefix = Recovered(c, selected)
      /\ CreatedRecoveryProposal(c, selected).first = RecoveryCreatedEntry(c, selected)
    BY DEF CreatedRecoveryProposal, Proposal
<1>9. canonical'[CreatedRecoveryProposal(c, selected).epoch]
          = Result(CreatedRecoveryProposal(c, selected))
    BY ONLY SMT, <1>1, <1>3, <1>8
<1>10. \A p \in proposals : canonical'[p.epoch] = canonical[p.epoch]
    BY ONLY SMT, <1>1, <1>2, <1>3 DEF ProposalCanonicalLinks
<1>11. \A p \in proposals :
           /\ p.epoch \in Terms /\ Result(p) \subseteq canonical'[p.epoch]
           /\ Prefix(canonical'[p.epoch], p.first.part - 1) = p.prefix
           /\ \A e \in canonical'[p.epoch] \ Result(p) :
                 e.term = p.epoch /\ e.index > p.first.index /\ e.part >= p.first.part
    BY ONLY ZenonT(5), <1>1, <1>10 DEF ProposalCanonicalLinks
<1>12. ProposalCanonicalLinks(canonical', {CreatedRecoveryProposal(c, selected)})
    BY ONLY SMT, <1>1, <1>7, <1>8, <1>9 DEF ProposalCanonicalLinks
<1> QED BY ONLY ZenonT(5), <1>4, <1>11, <1>12 DEF ProposalCanonicalLinks

THEOREM ProposalCanonicalLinksInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, ProofNext, term' \in [Replicas -> Terms]
    PROVE ProposalCanonicalLinks(canonical', proposals')
<1>1. ProtocolNext /\ GhostNext
    BY DEF ProofNext, Next
<1>2. CASE \E c \in Replicas : \E selected : BuildRecovery(c, selected)
    BY RecoveryKeepsProposalLinks, <1>1, <1>2
<1>3. CASE NormalCreation
    BY NormalCreationKeepsProposalLinks, <1>1, <1>3 DEF NormalCreation
<1>4. CASE ~NormalCreation /\ ~\E c \in Replicas : \E selected : BuildRecovery(c, selected)
    <2>1. PostLeaderBound /\ UNCHANGED proposals
        BY OnlyNormalCreationExtendsLeaderCanonical, OnlyRecoveryCreatesProposal, <1>1, <1>4
    <2>2. UNCHANGED canonical
        BY NoNewSourceKeepsCanonical, <1>1, <2>1
    <2> QED BY CandidateProposalCanonicalLinks, <2>1, <2>2
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
