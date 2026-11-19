---------------------- MODULE TRaftBoundaryCountSupport ---------------------
EXTENDS TRaftBoundaryProof, TRaftRecoveryMergeProof
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

LogBoundaryCounts(L) == \A e \in L : e.prevSize = Count(L, e.part - 1)
AllLogBoundaryCounts == \A r \in Replicas : LogBoundaryCounts(formal[r])
LogBoundaryFacts(L) == LogBoundaryCounts(L) /\ \A e \in L : e.part \in Int
AllLogBoundaryFacts == \A r \in Replicas : LogBoundaryFacts(formal[r])
LeaderBoundaryFacts(R, F) == \A r \in Replicas : R[r] = "Leader" => LogBoundaryFacts(F[r])
ProposalBoundaryCounts(P) == \A p \in P : p.first.prevSize = Count(p.prefix, p.first.part - 1)

THEOREM FiniteLogPartitionFrontier ==
    ASSUME NEW L, L \subseteq Entries, IsFiniteSet(L)
    PROVE Cur(L) \in Int /\ \A e \in L : e.part \in Int /\ e.part <= Cur(L)
<1>1. CASE L = {}
    BY SMT, <1>1, EmptyLogFrontier
<1>2. CASE L # {}
    BY SMT, <1>2, FiniteLogFrontier DEF Entries, Partitions
<1> QED BY <1>1, <1>2

THEOREM CandidateHasLogBoundaryCounts == ProofInvariant => AllLogBoundaryCounts
<1>1. ASSUME ProofInvariant, NEW r \in Replicas
      PROVE LogBoundaryCounts(formal[r])
    <2>1. formal[r] \subseteq Entries /\ ContextSound(formal[r]) /\ EntryBoundaryCounts
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
    <2> QED BY ContextCountsTransferToLog, <2>1 DEF LogBoundaryCounts
<1> QED BY <1>1 DEF AllLogBoundaryCounts

THEOREM CandidateHasLogBoundaryFacts == ProofInvariant => AllLogBoundaryFacts
BY SMT, CandidateHasLogBoundaryCounts DEF AllLogBoundaryCounts, AllLogBoundaryFacts,
   LogBoundaryFacts, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
   TypeOK, Entries, Partitions

THEOREM CandidateHasProposalBoundaryCounts == ProofInvariant => ProposalBoundaryCounts(proposals)
<1>1. ASSUME ProofInvariant, NEW p \in proposals
      PROVE p.first.prevSize = Count(p.prefix, p.first.part - 1)
    <2>1. p.prefix \subseteq Entries /\ IsFiniteSet(Result(p))
          /\ p.first.part = Cur(p.prefix) + 1
          /\ p.first.prevSize = Count(p.prefix, Cur(p.prefix))
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
            TypeOK, FiniteLogInvariant, FiniteProposals
    <2>2. IsFiniteSet(p.prefix)
        BY SMT, <2>1, FS_Subset DEF Result
    <2>3. Cur(p.prefix) \in Int
        BY FiniteLogPartitionFrontier, <2>1, <2>2
    <2> QED BY SMT, <2>1, <2>3
<1> QED BY <1>1 DEF ProposalBoundaryCounts

THEOREM AppendPreservesBoundaryCounts ==
    ASSUME NEW L, NEW e, LogBoundaryCounts(L), e.part \in Int,
           \A x \in L : x.part \in Int /\ x.part <= e.part,
           e.prevSize = Count(L, e.part - 1)
    PROVE LogBoundaryCounts(L \cup {e})
<1>0. e.part \in Int /\ \A x \in L : x.part \in Int /\ x.part <= e.part
    OBVIOUS
<1>1. \A x \in L : Count(L \cup {e}, x.part - 1) = Count(L, x.part - 1)
    <2>1. ASSUME NEW x \in L
          PROVE Count(L \cup {e}, x.part - 1) = Count(L, x.part - 1)
        <3>1. e.part # x.part - 1
            BY ONLY SMT, <1>0, <2>1
        <3> QED BY ONLY CountUnchangedOutsidePartition, <3>1
    <2> QED BY <2>1
<1>2. Count(L \cup {e}, e.part - 1) = Count(L, e.part - 1)
    BY SMT, CountUnchangedOutsidePartition
<1> QED BY SMT, <1>1, <1>2 DEF LogBoundaryCounts

THEOREM AppendPreservesBoundaryFacts ==
    ASSUME NEW L, NEW e, LogBoundaryFacts(L), e.part \in Int,
           \A x \in L : x.part <= e.part,
           e.prevSize = Count(L, e.part - 1)
    PROVE LogBoundaryFacts(L \cup {e})
BY SMT, AppendPreservesBoundaryCounts DEF LogBoundaryFacts

THEOREM BoundaryFactsUnderUpdate ==
    ASSUME AllLogBoundaryFacts, formal \in [Replicas -> SUBSET Entries],
           role \in [Replicas -> Roles], NEW r \in Replicas, NEW L,
           formal' = [formal EXCEPT ![r] = L], UNCHANGED role,
           role[r] = "Leader" => LogBoundaryFacts(L)
    PROVE LeaderBoundaryFacts(role', formal')
BY SMT DEF AllLogBoundaryFacts, LeaderBoundaryFacts

THEOREM PostContextsWithCounts ==
    ASSUME EntryBoundaryCounts, Observe,
           LeaderBoundaryFacts(role', formal'), ProposalBoundaryCounts(proposals')
    PROVE EntryBoundaryCounts'
<1>1. \A r \in Replicas : role'[r] = "Leader" => \A e \in formal'[r] :
          Count(Prefix(formal'[r], e.part - 1), e.part - 1) = Count(formal'[r], e.part - 1)
    <2>1. ASSUME NEW r \in Replicas, role'[r] = "Leader", NEW e \in formal'[r]
          PROVE Count(Prefix(formal'[r], e.part - 1), e.part - 1) = Count(formal'[r], e.part - 1)
        <3>1. Part(Prefix(formal'[r], e.part - 1), e.part - 1) = Part(formal'[r], e.part - 1)
            BY SMT, <2>1 DEF Part, Prefix, LeaderBoundaryFacts, LogBoundaryFacts
        <3> QED BY <3>1 DEF Count
    <2> QED BY <2>1
<1>2. entryContexts' = entryContexts \cup
         (UNION { {[entry |-> e, prefix |-> Prefix(formal'[r], e.part - 1)] :
                    e \in {x \in formal'[r] : x.term = term'[r]}} :
                   r \in {n \in Replicas : role'[n] = "Leader"}}) \cup
         {[entry |-> p.first, prefix |-> p.prefix] : p \in proposals'}
    BY DEF Observe
<1> QED BY SMT, <1>1, <1>2 DEF EntryBoundaryCounts, LogBoundaryCounts, ProposalBoundaryCounts, LeaderBoundaryFacts, LogBoundaryFacts

THEOREM ExistingLeaderIgnoresOwnOffer ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW o, ReceiveEntry(r, o), role[r] = "Leader"
    PROVE o.entry \in formal[r] /\ formal' = formal
<1>1. o \in offers /\ o.epoch = term[r]
    BY DEF ReceiveEntry, CanReceive
<1>2. PICK v \in leaderViews : v.epoch = o.epoch /\ o.entry \in v.entries
    BY SMT, <1>1 DEF ProofInvariant, OfferProvenance
<1>3. o.entry \in canonical[term[r]] /\ formal[r] = canonical[term[r]]
    BY SMT, <1>1, <1>2 DEF ProofInvariant, CanonicalViewLinks, PreProvenanceInvariant,
       RecoveryInvariant, CanonicalShape
<1>4. formal \in [Replicas -> SUBSET Entries]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>5. o.entry \in formal[r] /\ formal[r] \cup {o.entry} = formal[r]
    BY ONLY SMT, <1>3
<1>6. formal' = [formal EXCEPT ![r] = formal[r] \cup {o.entry}]
    BY DEF ReceiveEntry
<1>7. formal' = formal
    BY ONLY SMT, <1>4, <1>5, <1>6
<1> QED BY ONLY <1>5, <1>7

THEOREM ExistingLeaderIgnoresOwnConfirmation ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW p, LearnConfirmation(r, p), role[r] = "Leader"
    PROVE Publish(r, p) = formal[r] /\ formal' = formal
<1>1. p \in retained[r] /\ term[r] = p.epoch /\ p \in proposals
    BY SMT DEF LearnConfirmation, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. Result(p) \subseteq canonical[term[r]] /\ formal[r] = canonical[term[r]]
    <2>1. term[r] \in Terms /\ role[r] = "Leader" /\ r \in Replicas
        BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>2. \A t \in Terms : \A q \in proposals : q.epoch = t => Result(q) \subseteq canonical[t]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>3. \A s \in Replicas : role[s] = "Leader" => formal[s] = canonical[term[s]]
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2> QED BY ONLY SMT, <1>1, <2>1, <2>2, <2>3
<1>3. formal \in [Replicas -> SUBSET Entries]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1> QED BY SMT, <1>2, <1>3 DEF LearnConfirmation, Publish, Result
=============================================================================
