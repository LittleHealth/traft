---------------------- MODULE TRaftRecoveredContextProof ---------------------
EXTENDS TRaftPartitionEvidenceProof
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

THEOREM ReportedPendingCurrentEntryUsesSelectedProposal ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)), NEW r \in Reporters(c),
           NEW q \in reports[c][r].pending, NEW e \in Result(q), e.term = p.epoch
    PROVE q = p /\ e \in Result(p)
<1>1. q \in proposals /\ q.epoch <= p.epoch /\ q.epoch \in Nat /\ p.epoch \in Nat
    BY ReportAnchorNoNewerThanSelected
<1>2. p \in proposals
    BY SMT, ReportedProposalsAreActual DEF Latest
<1>3. e \in canonical[q.epoch] /\ e.term <= q.epoch
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, TypeOK
<1>4. q.epoch = p.epoch
    BY SMT, <1>1, <1>3
<1>5. q = p
    BY SMT, <1>1, <1>2, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY <1>5

THEOREM ReportedCurrentEntryHasCompleteEarlierPrefix ==
    ASSUME ProofInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)), NEW r \in Reporters(c),
           NEW e \in reports[c][r].entries, e.term = p.epoch
    PROVE Prefix(canonical[p.epoch], e.part - 1) \subseteq reports[c][r].entries
<1>1. reports[c][r] \in reportMessages /\ reports[c][r].entries # {}
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Reporters
<1>2. PICK q \in reports[c][r].pending : q.epoch = LastTerm(reports[c][r].entries)
              /\ Result(q) \subseteq reports[c][r].entries
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>3. q \in proposals /\ q.epoch <= p.epoch /\ q.epoch \in Nat /\ p.epoch \in Nat
    BY ReportAnchorNoNewerThanSelected, <1>2
<1>4. reports[c][r].entries \subseteq canonical[q.epoch]
      /\ Prefix(reports[c][r].entries, Cur(reports[c][r].entries) - 1)
          = Prefix(canonical[q.epoch], Cur(reports[c][r].entries) - 1)
    BY SMT, <1>1, <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, Sublog
<1>5. e.term <= q.epoch /\ canonical[q.epoch] \subseteq Entries
    BY SMT, <1>3, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, TypeOK
<1>6. q.epoch = p.epoch
    BY SMT, <1>3, <1>5
<1>7. reports[c][r].entries \subseteq Entries /\ IsFiniteSet(reports[c][r].entries)
    BY SMT, <1>1, <1>4, <1>5 DEF ProofInvariant, PreProvenanceInvariant, FiniteLogInvariant, FiniteSnapshots
<1>8. Cur(reports[c][r].entries) \in Int
      /\ \A x \in reports[c][r].entries : x.part \in Int /\ x.part <= Cur(reports[c][r].entries)
    BY FiniteLogPartitionFrontier, <1>7
<1>9. e \in reports[c][r].entries
    OBVIOUS
<1>10. \A x \in canonical[q.epoch] : x.part \in Int
    BY ONLY SMT, <1>5 DEF Entries, Partitions
<1> QED BY ONLY SMT, <1>4, <1>6, <1>8, <1>9, <1>10 DEF Prefix

THEOREM RecoveredContainsSelectedEpochPrefixes ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipRecoveryUnion,
           NEW c \in Replicas, NEW p \in Latest(ReportedProposals(c))
    PROVE \A e \in Recovered(c, p) : Prefix(canonical[p.epoch], e.part - 1) \subseteq Recovered(c, p)
<1>00. p \in proposals
    BY ReportedProposalsAreActual DEF Latest
<1>01. \A q \in proposals : q \in ProposalRecords /\ q.epoch \in Terms /\ q.first.term = q.epoch
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>02. \A t \in Terms : \A q \in proposals : q.epoch = t =>
          Result(q) \subseteq canonical[t] /\ Prefix(canonical[t], q.first.part - 1) = q.prefix
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>03. NoProposal \notin ProposalRecords
    BY DEF NoProposal
<1>1. p \in proposals /\ p \in ProposalRecords /\ p.epoch \in Terms
      /\ p.first.term = p.epoch /\ p # NoProposal
      /\ Result(p) \subseteq canonical[p.epoch]
      /\ Prefix(canonical[p.epoch], p.first.part - 1) = p.prefix
    BY ONLY SMT, <1>00, <1>01, <1>02, <1>03
<1>2. Recovered(c, p) \subseteq canonical[p.epoch] /\ Result(p) \subseteq Recovered(c, p)
    BY RecoveredIsCanonicalSubset, <1>1 DEF Recovered
<1>3. canonical[p.epoch] \subseteq Entries /\ ContextSound(canonical[p.epoch])
    BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>4. ASSUME NEW e \in Recovered(c, p)
      PROVE Prefix(canonical[p.epoch], e.part - 1) \subseteq Recovered(c, p)
    <2>1. CASE e \in Result(p)
        <3>1. PICK ctx \in entryContexts : ctx.entry = e
                  /\ ctx.prefix = Prefix(canonical[p.epoch], e.part - 1)
            BY SMT, <1>2, <1>3, <1>4 DEF ContextSound
        <3>2. ctx.prefix \subseteq Result(p)
            BY RecoveryResultContainsEntryContext, <1>1, <2>1, <3>1
        <3> QED BY <1>2, <3>1, <3>2
    <2>2. CASE e \notin Result(p)
        <3>1. e \in ReportedEntries(c) /\ e.term = p.epoch
            BY SMT, <1>1, <1>4, <2>2 DEF Recovered
        <3>2. PICK r \in Reporters(c) : e \in reports[c][r].entries
                  \/ \E q \in reports[c][r].pending : e \in Result(q)
            BY SMT, <3>1 DEF ReportedEntries
        <3>3. e \in reports[c][r].entries
            BY SMT, ReportedPendingCurrentEntryUsesSelectedProposal, <2>2, <3>1, <3>2
        <3>4. Prefix(canonical[p.epoch], e.part - 1) \subseteq reports[c][r].entries
            BY ReportedCurrentEntryHasCompleteEarlierPrefix, <3>1, <3>2, <3>3
        <3>5. ASSUME NEW x \in Prefix(canonical[p.epoch], e.part - 1)
              PROVE x \in Recovered(c, p)
            <4>1. x \in canonical[p.epoch] /\ x.part \in Nat /\ p.first.part \in Nat
                  /\ x \in reports[c][r].entries
                BY SMT, <1>1, <1>3, <3>4, <3>5 DEF Prefix, Entries, Partitions, ProposalRecords
            <4>2. CASE x.part < p.first.part
                <5>1. x \in p.prefix
                    BY ONLY SMT, <1>1, <4>1, <4>2 DEF Prefix
                <5> QED BY SMT, <1>2, <5>1 DEF Result
            <4>3. CASE x.part >= p.first.part
                <5>1. x.term = p.epoch
                    BY CanonicalRecoveryExtensionHasCurrentOrigin, <1>1, <4>1, <4>3
                <5>2. x \in ReportedEntries(c)
                    BY SMT, <3>2, <4>1 DEF ReportedEntries
                <5> QED BY SMT, <1>1, <4>3, <5>1, <5>2 DEF Recovered
            <4> QED BY SMT, <4>1, <4>2, <4>3
        <3> QED BY <3>5
    <2> QED BY <2>1, <2>2
<1> QED BY <1>4

THEOREM RecoveryMergePreservesContexts ==
    ASSUME ProofInvariant, EntryContextUnique, ~MutSkipRecoveryUnion,
           NEW c \in Replicas, NEW p \in Latest(ReportedProposals(c))
    PROVE ContextSound(Recovered(c, p))
<1>00. p \in proposals
    BY ReportedProposalsAreActual DEF Latest
<1>01. \A q \in proposals : q.epoch \in Terms
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>02. \A t \in Terms : ContextSound(canonical[t])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>1. p \in proposals /\ p.epoch \in Terms /\ ContextSound(canonical[p.epoch])
    BY ONLY <1>00, <1>01, <1>02
<1>2. Recovered(c, p) \subseteq canonical[p.epoch]
    BY RecoveredIsCanonicalSubset
<1>3. \A e \in Recovered(c, p) : Prefix(canonical[p.epoch], e.part - 1) \subseteq Recovered(c, p)
    BY RecoveredContainsSelectedEpochPrefixes
<1>4. \A e \in Recovered(c, p) :
          Prefix(Recovered(c, p), e.part - 1) = Prefix(canonical[p.epoch], e.part - 1)
    BY ONLY SMT, <1>2, <1>3 DEF Prefix
<1> QED BY SMT, <1>1, <1>2, <1>4 DEF ContextSound
=============================================================================
