------------------------- MODULE TRaftSafetyConsequences ---------------------
EXTENDS TRaftAgreementFromInvariant, TRaftLogMatchingFromInvariant,
        TRaftRecoveryMergeProof, TRaftProposalEvidenceProof
USE ParameterAssumptions DEF ParameterAssumptions

\* State consequences of the candidate. No temporal safety theorem is
\* asserted here: preserving the candidate is a separate proof obligation.
THEOREM CandidateReportsHaveOrigin == ProofInvariant => RecoveryReportsHaveOrigin
<1>1. ASSUME ProofInvariant, NEW c \in Replicas, ReportedProposals(c) = {}
      PROVE ReportedEntries(c) = {}
    <2>1. \A r \in Reporters(c) : reports[c][r].pending = {}
        BY ONLY SMT, <1>1 DEF ReportedProposals
    <2>2. \A r \in Reporters(c) : reports[c][r] \in reportMessages
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, ControlInvariant, CollectedReportProvenance
    <2>3. \A m \in reportMessages : m.entries # {} =>
              \E p \in m.pending : p.epoch = LastTerm(m.entries) /\ Result(p) \subseteq m.entries
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
    <2>4. \A r \in Reporters(c) : reports[c][r].entries = {}
        BY ONLY ZenonT(5), <2>1, <2>2, <2>3
    <2> QED BY ONLY SMT, <2>1, <2>4 DEF ReportedEntries
<1> QED BY <1>1 DEF RecoveryReportsHaveOrigin

THEOREM CandidateImpliesQuorumProposalPreservation ==
    (ProofInvariant /\ CommitEvidenceSound) => QuorumProposalPreservation
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, NEW p \in proposals,
            Quorum(ProposalSenders(ackMessages, p))
      PROVE /\ \A q \in proposals : q.recovering /\ q.epoch > p.epoch => Result(p) \subseteq q.prefix
            /\ \A v \in leaderViews : v.epoch > p.epoch => Result(p) \subseteq v.entries
    <2>1. \A e \in Result(p) : [epoch |-> p.epoch, entry |-> e] \in commitHistory
        BY ChosenProposalHasEntryEvidence, <1>1
    <2>2. RecoveryPreservesCommitted /\ EntryLeaderCompleteness
        BY CandidateImpliesRecoveryPreservesCommitted, CandidateImpliesEntryLeaderCompleteness, <1>1
    <2> QED BY ONLY ZenonT(10), <2>1, <2>2 DEF RecoveryPreservesCommitted, EntryLeaderCompleteness
<1> QED BY <1>1 DEF QuorumProposalPreservation, ProposalSenders

DerivedSafety ==
    /\ CommitEvidenceAgreement /\ EntryLeaderCompleteness
    /\ RecoveryPreservesCommitted /\ RecoveryCandidatesPreserveEvidence
    /\ RecoveryReportsHaveOrigin /\ RecoveryUnionCoherent
    /\ StateMachineSafety /\ QuorumProposalPreservation
    /\ NormalCountCheckSound /\ LogMatching /\ IntraPartitionRankEquivalence

THEOREM CandidateSafetyConsequences ==
    (ProofInvariant /\ CommitEvidenceSound /\ EntryContextUnique /\ ~MutSkipRecoveryUnion) => DerivedSafety
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, EntryContextUnique, ~MutSkipRecoveryUnion
      PROVE DerivedSafety
    <2>1. CommitEvidenceAgreement /\ EntryLeaderCompleteness /\ RecoveryPreservesCommitted
        BY CandidateImpliesEvidenceAgreement, CandidateImpliesEntryLeaderCompleteness,
           CandidateImpliesRecoveryPreservesCommitted, <1>1
    <2>2. RecoveryCandidatesPreserveEvidence /\ RecoveryReportsHaveOrigin /\ RecoveryUnionCoherent
        BY CandidateRecoveryRetainsEvidence, CandidateReportsHaveOrigin, RecoveryMergeCoherentFromInvariant, <1>1
    <2>3. AppliedEvidence /\ ContextOrigins(canonical, entryContexts) /\ CanonicalShape
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, HistoryOriginInvariant
    <2>4. StateMachineSafety /\ QuorumProposalPreservation /\ NormalCountCheckSound
        BY CandidateWithAppliedEvidenceImpliesStateMachineSafety,
           CandidateImpliesQuorumProposalPreservation, CountSafetyFromCandidate, <1>1, <2>3
    <2>5. LogMatching
        BY ContextOriginsImplyLogMatching, <1>1, <2>3
    <2>6. IntraPartitionRankEquivalence
        BY LogMatchingImpliesRankEquivalence, <1>1, <2>5
    <2> QED BY <2>1, <2>2, <2>4, <2>5, <2>6 DEF DerivedSafety
<1> QED BY <1>1

\* Prime a proved, closed implication, not an assumed pre-state predicate.
\* Its primed premises must still be independently proved in the induction.
THEOREM CandidateSafetyConsequencesNext ==
    (ProofInvariant' /\ CommitEvidenceSound' /\ EntryContextUnique' /\ ~MutSkipRecoveryUnion) => DerivedSafety'
<1>1. CandidateSafetyConsequences'
    BY ONLY PTL, CandidateSafetyConsequences
<1> QED BY ONLY <1>1
=============================================================================
