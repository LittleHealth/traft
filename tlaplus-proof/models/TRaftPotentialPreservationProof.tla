-------------------- MODULE TRaftPotentialPreservationProof -------------------
EXTENDS TRaftPotentialProof, TRaftRecoveryProof, TRaftTermAndVoteProof,
        TRaftProposalIdentityProof
USE ParameterAssumptions, SentinelSeparation DEF ParameterAssumptions, SentinelSeparation

PostProposalPotential(P) == \A p \in P, t \in Terms, e \in IssuedEntries' :
    t < p.epoch /\ MayChoose(t, e)' => e \in p.prefix
PostViewPotential(V) == \A v \in V, t \in Terms, e \in IssuedEntries' :
    t < v.epoch /\ MayChoose(t, e)' => e \in v.entries

THEOREM CandidatePotentialTypes == ProofInvariant =>
    /\ term \in [Replicas -> Nat]
    /\ \A p \in proposals : p.epoch \in Nat /\ p \in ProposalRecords
    /\ \A v \in leaderViews : v.epoch \in Nat
BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK,
   CanonicalViewLinks, Terms

THEOREM LeaderViewHasEpochFence ==
    ASSUME ProofInvariant, NEW v \in leaderViews
    PROVE Quorum({r \in Replicas : term[r] >= v.epoch})
<1>1. PICK p \in confirmations : p.epoch = v.epoch
    BY DEF ProofInvariant, PrefixEvidenceInvariant, ActiveRecoveryCertificates, LeaderViewsCertified
<1>2. p \in proposals
    BY <1>1 DEF ProofInvariant, MessageSourceInvariant, ConfirmationSources
<1>3. \A q \in proposals : Quorum({r \in Replicas : term[r] >= q.epoch})
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, ReportFences
<1>4. Quorum({r \in Replicas : term[r] >= p.epoch})
    BY ONLY <1>2, <1>3
<1> QED BY ONLY <1>1, <1>4

THEOREM ExistingViewsKeepPotentialEntries ==
    ASSUME ProofInvariant, StepFacts, term' \in [Replicas -> Nat]
    PROVE PostViewPotential(leaderViews)
<1>1. term \in [Replicas -> Nat] /\ \A v \in leaderViews : v.epoch \in Nat
    BY CandidatePotentialTypes
<1>2. ASSUME NEW v \in leaderViews, NEW t \in Terms, NEW e \in IssuedEntries',
            t < v.epoch, MayChoose(t, e)'
      PROVE e \in v.entries
    <2>1. MayChoose(t, e) /\ t \in Nat
        BY SMT, PossibleMajoritiesOnlyShrink, <1>1, <1>2 DEF Terms
    <2>2. Quorum({r \in Replicas : term[r] >= v.epoch})
        BY LeaderViewHasEpochFence, <1>2
    <2>3. e \in IssuedEntries
        BY OldPotentialEntryAlreadyIssued, <1>1, <1>2, <2>1, <2>2
    <2> QED BY <1>2, <2>1, <2>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, PotentialPreservation
<1> QED BY <1>2 DEF PostViewPotential

THEOREM PotentialOldEntryForcesReportedProposal ==
    ASSUME ProofInvariant, NEW c \in Replicas, Quorum(Reporters(c)),
           NEW t \in Nat, NEW e, t < term[c], MayChoose(t, e)
    PROVE ReportedProposals(c) # {}
<1>1. term \in [Replicas -> Nat] /\ \A r \in Reporters(c) : term[r] >= term[c]
    BY CandidatePotentialTypes, ReportsFenceEarlierTerms
<1>2. PICK r \in Reporters(c) : r \in EpochAckers(t, e)
    BY FencedOldAck, <1>1
<1>3. PICK a \in ackMessages : a.sender = r /\ a.epoch = t /\ e \in a.contents
    BY SMT, <1>2 DEF EpochAckers
<1>4. PICK p \in retained[r] : p.epoch = t
    BY SMT, <1>3 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin
<1>5. p \in reports[c][r].pending
    BY SMT, <1>2, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, ReportFences, Reporters
<1> QED BY SMT, <1>2, <1>5 DEF ReportedProposals

THEOREM NewRecoveryKeepsPotentialEntries ==
    ASSUME ProofInvariant, ~MutSkipRecoveryUnion, StepFacts, term' \in [Replicas -> Nat],
           NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE PostProposalPotential(proposals' \ proposals)
<1>1. term \in [Replicas -> Nat] /\ \A p \in proposals : p \in ProposalRecords
    BY CandidatePotentialTypes
<1>20. BuildRecovery(c, selected)
    OBVIOUS
<1>21. ReportedProposals(c) \subseteq proposals /\ NoProposal \notin ProposalRecords
    BY ReportedProposalsAreActual DEF NoProposal
<1>22. selected = NoProposal => ReportedProposals(c) = {}
    BY ONLY SMT, <1>1, <1>20, <1>21 DEF BuildRecovery, Latest
<1>23. c \in Reporters(c) /\ Quorum(Reporters(c))
      /\ (selected # NoProposal => selected \in Latest(ReportedProposals(c)))
      /\ (\A p \in proposals' \ proposals : p.epoch = term[c] /\ p.prefix = Recovered(c, selected))
    BY ONLY SMT, <1>20 DEF BuildRecovery, Proposal
<1>2. c \in Reporters(c) /\ Quorum(Reporters(c))
      /\ (selected = NoProposal => ReportedProposals(c) = {})
      /\ (selected # NoProposal => selected \in Latest(ReportedProposals(c)))
      /\ (\A p \in proposals' \ proposals : p.epoch = term[c] /\ p.prefix = Recovered(c, selected))
    BY <1>22, <1>23
<1>3. ASSUME NEW p \in proposals' \ proposals, NEW t \in Terms, NEW e \in IssuedEntries',
            t < p.epoch, MayChoose(t, e)'
      PROVE e \in p.prefix
    <2>1. t \in Nat /\ t < term[c] /\ MayChoose(t, e)
        BY SMT, PossibleMajoritiesOnlyShrink, <1>1, <1>2, <1>3 DEF Terms
    <2>2. ReportedProposals(c) # {} /\ selected # NoProposal
        BY PotentialOldEntryForcesReportedProposal, <1>2, <2>1
    <2>3. e \in IssuedEntries
        <3>1. \A r \in Reporters(c) : term[r] >= term[c]
            BY ReportsFenceEarlierTerms
        <3>2. \E r \in Reporters(c) : r \in EpochAckers(t, e)
            BY FencedOldAck, <1>1, <1>2, <2>1, <3>1
        <3> QED BY SMT, <3>2 DEF EpochAckers, IssuedEntries
    <2>4. e \in Recovered(c, selected)
        BY RecoveryResultPreservesPossible, <1>1, <1>2, <1>3, <2>1, <2>2, <2>3
    <2> QED BY <1>2, <1>3, <2>4
<1> QED BY <1>3 DEF PostProposalPotential

THEOREM ProposalPotentialInductiveStep ==
    ASSUME ProofInvariant, ~MutSkipRecoveryUnion, StepFacts, ProtocolNext,
           term' \in [Replicas -> Nat]
    PROVE PostProposalPotential(proposals')
<1>1. term \in [Replicas -> Nat] /\ (\A p \in proposals : p.epoch \in Nat)
      /\ PotentialPreservation /\ ReportFences
    BY CandidatePotentialTypes DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>2. PostProposalPotential(proposals)
    BY ExistingProposalsKeepPotentialEntries, <1>1 DEF PostProposalPotential
<1>3. (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
          \/ UNCHANGED proposals
    BY OnlyRecoveryCreatesProposal
<1>4. PostProposalPotential(proposals' \ proposals)
    BY SMT, NewRecoveryKeepsPotentialEntries, <1>3 DEF PostProposalPotential
<1> QED BY SMT, <1>2, <1>4 DEF PostProposalPotential

THEOREM ObservedLeadersInheritProposalPotential ==
    ASSUME PostProposalPotential(proposals'), PostViewPotential(leaderViews),
           CanonicalShape', ControlInvariant', term' \in [Replicas -> Terms], Observe
    PROVE PostViewPotential(leaderViews')
<1>1. \A r \in Replicas : role'[r] = "Leader" =>
          current'[r] \in proposals' /\ current'[r].epoch = term'[r]
    BY SMT DEF ControlInvariant, ControlShape
<1>2. \A r \in Replicas : role'[r] = "Leader" =>
          Result(current'[r]) \subseteq formal'[r]
    BY SMT, <1>1 DEF CanonicalShape
<1>3. \A r \in Replicas : role'[r] = "Leader" =>
          \A t \in Terms, e \in IssuedEntries' : t < term'[r] /\ MayChoose(t, e)' => e \in formal'[r]
    BY SMT, <1>1, <1>2 DEF PostProposalPotential, Result
<1> QED BY SMT, <1>3 DEF Observe, PostViewPotential

THEOREM PotentialPreservationInductiveStep ==
    ASSUME ProofInvariant, ProofNext, ~MutSkipRecoveryUnion,
           CanonicalShape', ControlInvariant', term' \in [Replicas -> Terms]
    PROVE PotentialPreservation'
<1>1. ProtocolNext /\ Observe /\ StepFacts /\ term' \in [Replicas -> Nat]
    BY SMT, CandidateStepHasMonotonicFacts DEF ProofNext, Next, Terms
<1>2. PostProposalPotential(proposals')
    BY ProposalPotentialInductiveStep, <1>1
<1>3. PostViewPotential(leaderViews)
    BY ExistingViewsKeepPotentialEntries, <1>1
<1>4. PostViewPotential(leaderViews')
    BY ObservedLeadersInheritProposalPotential, <1>1, <1>2, <1>3
<1> QED BY <1>2, <1>4 DEF PotentialPreservation, PostProposalPotential, PostViewPotential
=============================================================================
