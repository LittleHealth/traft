----------------------- MODULE TRaftRecoveryMergeProof -----------------------
EXTENDS TRaftRecoveryProof, TRaftFiniteLogProof
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

THEOREM CoherenceInheritedBySubset ==
    ASSUME NEW L, NEW S, Coherent(L), S \subseteq L
    PROVE Coherent(S)
BY SMT DEF Coherent

THEOREM ReportAnchorNoNewerThanSelected ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)),
           NEW r \in Reporters(c), NEW q \in reports[c][r].pending
    PROVE q \in proposals /\ q.epoch <= p.epoch /\ q.epoch \in Nat /\ p.epoch \in Nat
<1>1. q \in ReportedProposals(c) /\ p \in ReportedProposals(c)
    BY SMT DEF ReportedProposals, Latest
<1>2. ReportedProposals(c) \subseteq proposals
    BY ReportedProposalsAreActual
<1>3. \A x \in ReportedProposals(c) : x.first.term = x.epoch /\ x.epoch \in Nat
    BY SMT, <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
<1> QED BY SMT, <1>1, <1>2, <1>3, SelectedEpochNotOlder

THEOREM ReportedResultCurrentTermSubset ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)), NEW r \in Reporters(c),
           NEW q \in reports[c][r].pending, NEW e \in Result(q), e.term = p.epoch
    PROVE e \in canonical[p.epoch]
<1>1. q \in proposals /\ q.epoch <= p.epoch /\ q.epoch \in Nat /\ p.epoch \in Nat
    BY ReportAnchorNoNewerThanSelected
<1>2. e \in canonical[q.epoch] /\ e.term <= q.epoch
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, TypeOK
<1>3. q.epoch = p.epoch
    BY SMT, <1>1, <1>2
<1> QED BY <1>2, <1>3

THEOREM ReportedLogCurrentTermSubset ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)), NEW r \in Reporters(c),
           NEW e \in reports[c][r].entries, e.term = p.epoch
    PROVE e \in canonical[p.epoch]
<1>1. reports[c][r] \in reportMessages /\ reports[c][r].entries # {}
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Reporters
<1>2. PICK q \in reports[c][r].pending : q.epoch = LastTerm(reports[c][r].entries)
                  /\ Result(q) \subseteq reports[c][r].entries
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>3. q \in proposals /\ q.epoch <= p.epoch /\ q.epoch \in Nat /\ p.epoch \in Nat
    BY ReportAnchorNoNewerThanSelected, <1>2
<1>4. reports[c][r].entries \subseteq canonical[q.epoch]
    BY SMT, <1>1, <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Sublog
<1>5. e.term <= q.epoch
    BY SMT, <1>3, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, TypeOK
<1>6. q.epoch = p.epoch
    BY SMT, <1>3, <1>5
<1> QED BY SMT, <1>4, <1>6

THEOREM RecoveredIsCanonicalSubset ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c))
    PROVE Recovered(c, p) \subseteq canonical[p.epoch]
<1>1. p \in proposals
    BY SMT, ReportedProposalsAreActual DEF Latest
<1>20. p \in ProposalRecords /\ p.epoch \in Terms /\ p.first.term = p.epoch
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>21. Absent \notin ProposalRecords
    BY DEF SentinelSeparation
<1>220. \A t \in Terms : \A q \in proposals : q.epoch = t => Result(q) \subseteq canonical[t]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>22. Result(p) \subseteq canonical[p.epoch]
    BY ONLY <1>220, <1>1, <1>20
<1>2. p.first.term = p.epoch /\ p # NoProposal /\ Result(p) \subseteq canonical[p.epoch]
    BY ONLY SMT, <1>20, <1>21, <1>22 DEF NoProposal
<1>3. \A e \in ReportedEntries(c) : e.term = p.epoch => e \in canonical[p.epoch]
    BY SMT, ReportedResultCurrentTermSubset, ReportedLogCurrentTermSubset DEF ReportedEntries
<1> QED BY SMT, <1>2, <1>3 DEF Recovered

THEOREM RecoveryMergeCoherentFromInvariant == ProofInvariant => RecoveryUnionCoherent
<1>1. ASSUME ProofInvariant, NEW c \in Replicas, NEW p \in Latest(ReportedProposals(c))
      PROVE Coherent(Recovered(c, p))
    <2>1. Recovered(c, p) \subseteq canonical[p.epoch]
        BY RecoveredIsCanonicalSubset, <1>1
    <2>2. p \in proposals
        BY SMT, <1>1, ReportedProposalsAreActual DEF Latest
    <2>30. p.epoch \in Terms
        BY SMT, <1>1, <2>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>31. \A t \in Terms : Coherent(canonical[t])
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>3. Coherent(canonical[p.epoch])
        BY ONLY <2>30, <2>31
    <2> QED BY CoherenceInheritedBySubset, <2>1, <2>3
<1> QED BY <1>1 DEF RecoveryUnionCoherent
=============================================================================
