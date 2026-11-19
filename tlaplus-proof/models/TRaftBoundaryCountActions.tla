--------------------- MODULE TRaftBoundaryCountActions ----------------------
EXTENDS TRaftBoundaryCountFrames

THEOREM BoundaryCountsFrame ==
    ASSUME ProofInvariant, UNCHANGED <<formal, proposals>>
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
BY SMT, CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
   DEF AllLogBoundaryFacts, LeaderBoundaryFacts

THEOREM BuildRecoveryBoundaryCounts ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>1. DEFINE L == Recovered(c, selected)
            e == Entry(LastIndex(L) + 1, term[c], Cur(L) + 1,
                       NoValue, "noop", Count(L, Cur(L)))
            p == Proposal(c, term[c], L, e, TRUE)
<1>2. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>3. Cur(L) \in Int
    <2>1. CASE ReportedProposals(c) = {}
        <3>1. L = {}
            BY SMT, <2>1 DEF BuildRecovery, L, Recovered
        <3> QED BY SMT, <3>1, EmptyLogFrontier
    <2>2. CASE ReportedProposals(c) # {}
        <3>1. selected \in Latest(ReportedProposals(c))
            BY <2>2 DEF BuildRecovery
        <3>2. L \subseteq canonical[selected.epoch]
            BY RecoveredIsCanonicalSubset, <3>1 DEF L
        <3>3. selected \in proposals /\ selected.epoch \in Terms
            BY SMT, ReportedProposalsAreActual, <3>1
               DEF Latest, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
        <3>4. canonical[selected.epoch] \subseteq Entries /\ IsFiniteSet(canonical[selected.epoch])
            BY SMT, <3>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
               CanonicalShape, CanonicalFinite
        <3>5. L \subseteq Entries /\ IsFiniteSet(L)
            BY SMT, <3>2, <3>4, FS_Subset
        <3> QED BY FiniteLogPartitionFrontier, <3>5
    <2> QED BY <2>1, <2>2
<1>4. p.first.prevSize = Count(p.prefix, p.first.part - 1)
    BY SMT, <1>3 DEF p, e, Entry, Proposal
<1>5. UNCHANGED formal /\ proposals' = proposals \cup {p}
    BY DEF BuildRecovery, p, e, L
<1> QED BY ONLY ZenonT(10), <1>2, <1>4, <1>5
    DEF LeaderBoundaryFacts, AllLogBoundaryFacts, ProposalBoundaryCounts

THEOREM CreateEntryBoundaryCounts ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW v, CreateEntry(c, v)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>0. c \in Replicas
    OBVIOUS
<1>1. DEFINE L == formal[c]
            e == Entry(LastIndex(L) + 1, term[c], Cur(L), v, "data", Count(L, Cur(L) - 1))
<1>2. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>3. L \subseteq Entries /\ IsFiniteSet(L)
      /\ formal \in [Replicas -> SUBSET Entries] /\ role \in [Replicas -> Roles]
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, FiniteLogInvariant, FiniteNodeData, L
<1>4. Cur(L) \in Int /\ \A x \in L : x.part \in Int /\ x.part <= Cur(L)
    BY FiniteLogPartitionFrontier, <1>3
<1>40. LogBoundaryFacts(L)
    BY SMT, <1>2 DEF AllLogBoundaryFacts, L
<1>41. e.part \in Int /\ (\A x \in L : x.part <= e.part)
       /\ e.prevSize = Count(L, e.part - 1)
    BY ONLY SMT, <1>4 DEF e, Entry
<1>5. LogBoundaryFacts(L \cup {e})
    BY ONLY AppendPreservesBoundaryFacts, <1>40, <1>41
<1>6. formal' = [formal EXCEPT ![c] = L \cup {e}] /\ UNCHANGED <<role, proposals>>
    BY DEF CreateEntry, L, e
<1> QED BY ONLY ZenonT(10), BoundaryFactsUnderUpdate, <1>0, <1>2, <1>3, <1>5, <1>6

THEOREM CreateSuccessorBoundaryCounts ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>0. c \in Replicas
    OBVIOUS
<1>1. DEFINE L == formal[c]
            e == Entry(LastIndex(L) + 1, term[c], Cur(L) + 1, v, k, Count(L, Cur(L)))
<1>2. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>3. L \subseteq Entries /\ IsFiniteSet(L)
      /\ formal \in [Replicas -> SUBSET Entries] /\ role \in [Replicas -> Roles]
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, FiniteLogInvariant, FiniteNodeData, L
<1>4. Cur(L) \in Int /\ \A x \in L : x.part \in Int /\ x.part <= Cur(L)
    BY FiniteLogPartitionFrontier, <1>3
<1>40. LogBoundaryFacts(L)
    BY SMT, <1>2 DEF AllLogBoundaryFacts, L
<1>41. e.part \in Int /\ (\A x \in L : x.part <= e.part)
       /\ e.prevSize = Count(L, e.part - 1)
    BY ONLY SMT, <1>4 DEF e, Entry
<1>5. LogBoundaryFacts(L \cup {e})
    BY ONLY AppendPreservesBoundaryFacts, <1>40, <1>41
<1>6. formal' = [formal EXCEPT ![c] = L \cup {e}] /\ UNCHANGED <<role, proposals>>
    BY DEF CreateSuccessor, L, e
<1> QED BY ONLY ZenonT(10), BoundaryFactsUnderUpdate, <1>0, <1>2, <1>3, <1>5, <1>6

THEOREM ReceiveBoundaryCounts ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>0. r \in Replicas
    OBVIOUS
<1>1. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>2. formal \in [Replicas -> SUBSET Entries] /\ role \in [Replicas -> Roles]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>3. role[r] = "Leader" => o.entry \in formal[r]
    BY ExistingLeaderIgnoresOwnOffer
<1>4. role[r] = "Leader" => LogBoundaryFacts(formal[r] \cup {o.entry})
    BY SMT, <1>1, <1>3 DEF AllLogBoundaryFacts
<1>5. formal' = [formal EXCEPT ![r] = formal[r] \cup {o.entry}]
      /\ UNCHANGED <<role, proposals>>
    BY DEF ReceiveEntry
<1> QED BY ONLY ZenonT(10), BoundaryFactsUnderUpdate, <1>0, <1>1, <1>2, <1>4, <1>5

THEOREM ConfirmBoundaryCounts ==
    ASSUME ProofInvariant, NEW c \in Replicas, ConfirmProposal(c)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>0. c \in Replicas
    OBVIOUS
<1>1. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>2. formal \in [Replicas -> SUBSET Entries] /\ role \in [Replicas -> Roles]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>3. role[c] # "Leader" /\ formal' = [formal EXCEPT ![c] = Publish(c, current[c])]
      /\ UNCHANGED <<role, proposals>>
    BY SMT DEF ConfirmProposal
<1> QED BY ONLY ZenonT(10), BoundaryFactsUnderUpdate, <1>0, <1>1, <1>2, <1>3

THEOREM LearnConfirmationBoundaryCounts ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
    PROVE LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
<1>0. r \in Replicas
    OBVIOUS
<1>1. AllLogBoundaryFacts /\ ProposalBoundaryCounts(proposals)
    BY CandidateHasLogBoundaryFacts, CandidateHasProposalBoundaryCounts
<1>2. formal \in [Replicas -> SUBSET Entries] /\ role \in [Replicas -> Roles]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>3. role[r] = "Leader" => Publish(r, p) = formal[r]
    BY ExistingLeaderIgnoresOwnConfirmation
<1>4. role[r] = "Leader" => LogBoundaryFacts(Publish(r, p))
    BY SMT, <1>1, <1>3 DEF AllLogBoundaryFacts
<1>5. formal' = [formal EXCEPT ![r] = Publish(r, p)] /\ UNCHANGED <<role, proposals>>
    BY DEF LearnConfirmation
<1> QED BY ONLY ZenonT(10), BoundaryFactsUnderUpdate, <1>0, <1>1, <1>2, <1>4, <1>5
=============================================================================
