-------------------------- MODULE TRaftRecoveryProof -------------------------
EXTENDS TRaftProofState, TRaftQuorumProof, TLAPS
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

THEOREM ReportedProposalsAreActual ==
    ASSUME ProofInvariant, NEW c \in Replicas
    PROVE ReportedProposals(c) \subseteq proposals
<1>1. retained \in [Replicas -> SUBSET proposals] /\
      \A r, s \in Replicas : reports[r][s] = NoReport \/ reports[r][s] \in reportMessages
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. \A m \in reportMessages :
          m.sender \in Replicas /\ m.pending \subseteq retained[m.sender]
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences
<1>3. \A r \in Reporters(c) : reports[c][r] \in reportMessages
    BY ONLY SMT, <1>1 DEF Reporters
<1>4. \A r \in Reporters(c) : reports[c][r].pending \subseteq proposals
    BY ONLY SMT, <1>1, <1>2, <1>3
<1> QED BY ONLY ZenonT(5), <1>4 DEF ReportedProposals

THEOREM ReportsFenceEarlierTerms ==
    ASSUME ProofInvariant, NEW c \in Replicas
    PROVE \A r \in Reporters(c) : term[r] >= term[c]
BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, ReportFences, TermAndVoteFacts, Reporters

THEOREM FencedOldAck ==
    ASSUME NEW c \in Replicas, NEW t \in Nat, NEW e,
           term \in [Replicas -> Nat], t < term[c],
           Quorum(Reporters(c)), MayChoose(t, e),
           \A r \in Reporters(c) : term[r] >= term[c]
    PROVE \E r \in Reporters(c) : r \in EpochAckers(t, e)
<1>1. \A r \in Reporters(c) : term[r] > t
    BY SMT DEF Reporters
<1>2. Majority(Replicas, Reporters(c))
      /\ Majority(Replicas, Possible(Replicas, ackMessages, term, t, e))
    BY DEF Quorum, Majority, MayChoose, PossibleAckers, EpochAckers, Possible, Senders
<1>3. \E r \in Reporters(c) : r \in Senders(Replicas, ackMessages, t, e)
    BY SMT, <1>1, <1>2, ReportQuorumHasOldAck
<1> QED BY SMT, <1>3 DEF EpochAckers, Senders

THEOREM SelectedEpochNotOlder ==
    ASSUME NEW Ps, NEW p \in Latest(Ps), NEW base \in Ps,
           \A q \in Ps : q.first.term = q.epoch /\ q.epoch \in Nat
    PROVE base.epoch <= p.epoch
BY SMT DEF Latest, Later

THEOREM FencedReportHasEntry ==
    ASSUME PotentialCoverage, NEW m \in reportMessages, NEW a \in ackMessages,
           NEW e \in a.contents, a.sender = m.sender, a.epoch < m.epoch,
           MayChoose(a.epoch, e)
    PROVE e \in ReportContents(m)
BY SMT DEF PotentialCoverage

THEOREM RecoveryIncludesResult ==
    ASSUME NEW c, NEW p, p # NoProposal
    PROVE Result(p) \subseteq Recovered(c, p)
BY SMT DEF Recovered

THEOREM RecoveryIncludesExtension ==
    ASSUME ~MutSkipRecoveryUnion, NEW c, NEW p, p # NoProposal,
           NEW e \in ReportedEntries(c), e.term = p.first.term,
           e.part >= p.first.part
    PROVE e \in Recovered(c, p)
BY SMT DEF Recovered

\* Conditional inductive recovery obligation. The OLD proposals satisfy
\* PotentialPreservation; the newly computed Recovered(c,p) is the conclusion.
\* ProofInvariant itself is still an unproved induction candidate.
THEOREM RecoveryResultPreservesPossible ==
    ASSUME ProofInvariant, ~MutSkipRecoveryUnion,
           term \in [Replicas -> Nat],
           NEW c \in Replicas, c \in Reporters(c), Quorum(Reporters(c)),
           NEW p \in Latest(ReportedProposals(c)),
           NEW t \in Terms, t \in Nat, NEW e \in IssuedEntries,
           t < term[c], MayChoose(t, e),
           \A q \in proposals : q \in ProposalRecords
    PROVE e \in Recovered(c, p)
<1>1. \A r \in Reporters(c) : term[r] >= term[c]
    BY ReportsFenceEarlierTerms
<1>2. \E r \in Reporters(c) : r \in EpochAckers(t, e)
    BY FencedOldAck, <1>1
<1>3. PICK r \in Reporters(c) : r \in EpochAckers(t, e)
    BY <1>2
<1>4. PICK a \in ackMessages : a.sender = r /\ a.epoch = t /\ e \in a.contents
    BY SMT, <1>3 DEF EpochAckers
<1>5. PICK base \in retained[r] :
         /\ base.epoch = t
         /\ \/ a.contents = Result(base)
            \/ /\ a.contents = {a.target} /\ a.target.term = t
               /\ a.target.part >= base.first.part
    BY SMT, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin
<1>6. base \in reports[c][r].pending /\ base \in proposals
    BY SMT, <1>3, <1>5 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, ReportFences, Reporters
<1>7. base \in ReportedProposals(c) /\ p \in proposals
    BY SMT, <1>3, <1>6, ReportedProposalsAreActual DEF ReportedProposals, Latest
<1>8. \A q \in ReportedProposals(c) : q.first.term = q.epoch /\ q.epoch \in Nat
    <2>1. ReportedProposals(c) \subseteq proposals
        BY ReportedProposalsAreActual
    <2>2. \A q \in proposals : q.first.term = q.epoch /\ q.epoch \in Nat
        BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
    <2> QED BY SMT, <2>1, <2>2
<1>9. t <= p.epoch /\ p.epoch \in Nat
    <2>1. p \in ReportedProposals(c)
        BY DEF Latest
    <2>2. base.epoch <= p.epoch
        BY ONLY SelectedEpochNotOlder, <1>7, <1>8
    <2>3. p.epoch \in Nat
        BY ONLY <2>1, <1>8
    <2> QED BY ONLY SMT, <1>5, <2>2, <2>3
<1>10. p # NoProposal
    BY SMT, <1>7 DEF NoProposal
<1>11. CASE t < p.epoch
    <2>1. e \in p.prefix
        BY SMT, <1>7, <1>11 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, PotentialPreservation
    <2> QED BY SMT, <2>1, <1>10, RecoveryIncludesResult DEF Result
<1>12. CASE t = p.epoch
    <2>1. base = p
        BY SMT, <1>5, <1>6, <1>7, <1>12 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>2. reports[c][r] \in reportMessages /\ reports[c][r].sender = a.sender
          /\ a.epoch < reports[c][r].epoch /\ MayChoose(a.epoch, e)
        BY SMT, <1>3, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, ReportFences, Reporters
    <2>3. PotentialCoverage
        BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2>4. e \in ReportContents(reports[c][r])
        BY FencedReportHasEntry, <1>4, <2>2, <2>3
    <2>5. e \in ReportedEntries(c)
        BY SMT, <1>3, <2>4 DEF ReportContents, ReportedEntries
    <2>6. p.first.term = p.epoch
        BY SMT, <1>7 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2> QED BY SMT, <1>4, <1>5, <1>10, <2>1, <2>5, <2>6,
               RecoveryIncludesResult, RecoveryIncludesExtension
<1> QED BY SMT, <1>9, <1>11, <1>12
=============================================================================
