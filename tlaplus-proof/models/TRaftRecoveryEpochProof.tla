------------------------- MODULE TRaftRecoveryEpochProof ---------------------
EXTENDS TRaftCanonicalTransitionSupport, TRaftRecoveryMergeProof

THEOREM CollectedProposalEpochBound ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW p \in ReportedProposals(c)
    PROVE p.epoch <= term[c] /\ p.epoch \in Nat /\ term[c] \in Nat
<1>1. PICK r \in Reporters(c) : p \in reports[c][r].pending
    BY DEF ReportedProposals
<1>2. reports[c][r] \in reportMessages /\ reports[c][r].epoch = term[c]
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, ControlInvariant, CollectedReportProvenance
<1>3. \A m \in reportMessages : \A q \in m.pending : q.epoch <= m.epoch
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>4. p \in proposals /\ term[c] \in Nat
    BY SMT, ReportedProposalsAreActual DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
<1>5. p.epoch \in Nat
    BY SMT, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM RecoverySelectsOlderEpoch ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, NEW p,
           BuildRecovery(c, p), p \in ReportedProposals(c)
    PROVE p.epoch < term[c]
<1>1. p.epoch <= term[c] /\ p.epoch \in Nat /\ term[c] \in Nat
    BY CollectedProposalEpochBound
<1>2. p \in proposals /\ ControlInvariant /\ ElectionInvariant
      /\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
    BY ReportedProposalsAreActual DEF ProofInvariant, PreProvenanceInvariant, BuildRecovery
<1>3. [node |-> c, epoch |-> term[c]] \in winners
    BY SMT, <1>2 DEF ElectionInvariant, ElectionWinnerFacts
<1>4. ~\E q \in proposals : q.epoch = term[c]
    BY RecoveryCreatorHasFreshEpoch, <1>2, <1>3
<1> QED BY ONLY SMT, <1>1, <1>2, <1>4

THEOREM RecoveryOnlyCopiesOlderCreationTerms ==
    ASSUME ProofInvariant, ElectionSafety, NEW c \in Replicas, NEW p, BuildRecovery(c, p)
    PROVE \A e \in Recovered(c, p) : e.term < term[c]
<1>1. CASE ReportedProposals(c) = {}
    BY SMT, <1>1 DEF BuildRecovery, Recovered
<1>2. CASE ReportedProposals(c) # {}
    <2>1. p \in Latest(ReportedProposals(c)) /\ p \in ReportedProposals(c)
        BY SMT, <1>2 DEF BuildRecovery, Latest
    <2>2. p.epoch < term[c] /\ p.epoch \in Nat /\ term[c] \in Nat
        BY RecoverySelectsOlderEpoch, CollectedProposalEpochBound, <2>1
    <2>3. Recovered(c, p) \subseteq canonical[p.epoch]
        BY RecoveredIsCanonicalSubset, <2>1
    <2>4. p \in proposals /\ p.epoch \in Terms
        BY SMT, ReportedProposalsAreActual, <2>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>5. \A e \in canonical[p.epoch] : e.term \in Nat /\ e.term <= p.epoch
        BY SMT, <2>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Entries, Terms
    <2> QED BY ONLY SMT, <2>2, <2>3, <2>5
<1> QED BY <1>1, <1>2

THEOREM BuildRecoveryPreservesProposalBoundaries ==
    ASSUME ProofInvariant, ElectionSafety, RecoveryProposalBoundaries(proposals),
           NEW c \in Replicas, NEW p, BuildRecovery(c, p)
    PROVE RecoveryProposalBoundaries(proposals')
<1>1. \A e \in Recovered(c, p) : e.term < term[c]
    BY RecoveryOnlyCopiesOlderCreationTerms
<1>2. \A q \in proposals' \ proposals :
          q.first.kind = "noop" /\ q.prefix = Recovered(c, p) /\ q.epoch = term[c]
    BY SMT DEF BuildRecovery, Proposal, Entry
<1>3. RecoveryProposalBoundaries(proposals)
    OBVIOUS
<1> QED BY ONLY SMT, <1>1, <1>2, <1>3 DEF RecoveryProposalBoundaries

THEOREM RecoveryProposalBoundariesInductiveStep ==
    ASSUME ProofInvariant, ElectionSafety, RecoveryProposalBoundaries(proposals), ProtocolNext
    PROVE RecoveryProposalBoundaries(proposals')
<1>1. (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
      \/ UNCHANGED proposals
    BY OnlyRecoveryCreatesProposal
<1> QED BY BuildRecoveryPreservesProposalBoundaries, <1>1
=============================================================================
