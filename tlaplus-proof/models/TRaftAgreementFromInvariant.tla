--------------------- MODULE TRaftAgreementFromInvariant ---------------------
EXTENDS TRaftRecoveryProof, TRaftCommitSupport, TRaftHistoryOriginState
USE ParameterAssumptions DEF ParameterAssumptions

\* Conditional consequences, not a substitute for preserving ProofInvariant.
THEOREM EvidenceIsPossible ==
    ASSUME CommitEvidenceSound, NEW f \in commitHistory
    PROVE f.epoch \in Terms \ {0} /\ f.entry \in IssuedEntries
          /\ MayChoose(f.epoch, f.entry)
<1>1. f \in Evidence(ackMessages)
    BY DEF CommitEvidenceSound
<1>2. f.epoch \in Terms \ {0} /\ f.entry \in IssuedEntries
    BY SMT, <1>1 DEF Evidence, IssuedEntries
<1>3. PICK c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
    BY IndependentEvidenceHasActualDistinctSenders, <1>1
<1>4. MessageAckers(ackMessages, c, f.epoch, f.entry) \subseteq
          Senders(Replicas, ackMessages, f.epoch, f.entry)
    BY SMT DEF MessageAckers, Senders
<1>50. IsFiniteSet(Replicas) /\ Majority(Replicas, MessageAckers(ackMessages, c, f.epoch, f.entry))
    BY <1>3 DEF Quorum, Majority
<1>51. Majority(Replicas, Possible(Replicas, ackMessages, term, f.epoch, f.entry))
    BY ONLY AckedEntriesArePossible, <1>50, <1>4
<1>5. MayChoose(f.epoch, f.entry)
    BY ONLY <1>51 DEF MayChoose, Quorum, PossibleAckers, EpochAckers, Majority, Possible, Senders
<1> QED BY <1>2, <1>5

THEOREM EvidenceHasCanonicalSource ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW f \in commitHistory
    PROVE f.entry \in canonical[f.epoch]
<1>1. f \in Evidence(ackMessages)
    BY DEF CommitEvidenceSound
<1>2. PICK c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
    BY IndependentEvidenceHasActualDistinctSenders, <1>1
<1>3. MessageAckers(ackMessages, c, f.epoch, f.entry) # {}
    BY QuorumIsNonempty, <1>2
<1>4. PICK a \in ackMessages : a.epoch = f.epoch /\ f.entry \in a.contents
    BY SMT, <1>3 DEF MessageAckers
<1> QED BY SMT, <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin

THEOREM EarlierEvidenceBelongsToLaterCanonical ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW f \in commitHistory,
           NEW t \in Terms, canonical[t] # {}, f.epoch < t
    PROVE f.entry \in canonical[t]
<1>1. f.epoch \in Terms /\ f.entry \in IssuedEntries /\ MayChoose(f.epoch, f.entry)
    BY EvidenceIsPossible
<1>2. PICK p \in proposals : p.epoch = t
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts
<1>30. PotentialPreservation /\ f.epoch < t
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
<1>3. f.entry \in p.prefix
    BY ONLY SMT, <1>1, <1>2, <1>30 DEF PotentialPreservation
<1>4. Result(p) \subseteq canonical[t]
    BY SMT, <1>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY SMT, <1>3, <1>4 DEF Result

THEOREM CandidateImpliesEvidenceAgreement ==
    (ProofInvariant /\ CommitEvidenceSound) => CommitEvidenceAgreement
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, NEW a \in commitHistory,
            NEW b \in commitHistory, a.entry.index = b.entry.index
      PROVE a.entry = b.entry
    <2>1. a.epoch \in Terms /\ b.epoch \in Terms /\ a.epoch \in Nat /\ b.epoch \in Nat
        BY SMT, EvidenceIsPossible, <1>1 DEF Terms
    <2>2. a.entry \in canonical[a.epoch] /\ b.entry \in canonical[b.epoch]
        BY EvidenceHasCanonicalSource, <1>1
    <2>3. Coherent(canonical[a.epoch]) /\ Coherent(canonical[b.epoch])
        BY <1>1, <2>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
    <2>4. CASE a.epoch < b.epoch
        <3>1. a.entry \in canonical[b.epoch]
            BY EarlierEvidenceBelongsToLaterCanonical, <1>1, <2>1, <2>2, <2>4
        <3> QED BY SMT, <1>1, <2>2, <2>3, <3>1 DEF Coherent
    <2>5. CASE b.epoch < a.epoch
        <3>1. b.entry \in canonical[a.epoch]
            BY EarlierEvidenceBelongsToLaterCanonical, <1>1, <2>1, <2>2, <2>5
        <3> QED BY SMT, <1>1, <2>2, <2>3, <3>1 DEF Coherent
    <2>6. CASE a.epoch = b.epoch
        BY SMT, <1>1, <2>2, <2>3, <2>6 DEF Coherent
    <2> QED BY SMT, <2>1, <2>4, <2>5, <2>6
<1> QED BY <1>1 DEF CommitEvidenceAgreement

THEOREM CandidateImpliesEntryLeaderCompleteness ==
    (ProofInvariant /\ CommitEvidenceSound) => EntryLeaderCompleteness
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, NEW f \in commitHistory,
            NEW v \in leaderViews, v.epoch > f.epoch
      PROVE f.entry \in v.entries
    <2>1. f.epoch \in Terms /\ f.entry \in IssuedEntries /\ MayChoose(f.epoch, f.entry)
        BY EvidenceIsPossible, <1>1
    <2>2. PotentialPreservation
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2> QED BY ONLY ZenonT(5), <1>1, <2>1, <2>2 DEF PotentialPreservation
<1> QED BY <1>1 DEF EntryLeaderCompleteness

THEOREM CandidateImpliesRecoveryPreservesCommitted ==
    (ProofInvariant /\ CommitEvidenceSound) => RecoveryPreservesCommitted
<1>1. ASSUME ProofInvariant, CommitEvidenceSound, NEW f \in commitHistory,
            NEW p \in proposals, p.recovering, p.epoch > f.epoch
      PROVE f.entry \in p.prefix
    <2>1. f.epoch \in Terms /\ f.entry \in IssuedEntries /\ MayChoose(f.epoch, f.entry)
        BY EvidenceIsPossible, <1>1
    <2>2. PotentialPreservation
        BY <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant
    <2> QED BY ONLY ZenonT(5), <1>1, <2>1, <2>2 DEF PotentialPreservation
<1> QED BY <1>1 DEF RecoveryPreservesCommitted

THEOREM CandidateRecoveryRetainsEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, ~MutSkipRecoveryUnion
    PROVE RecoveryCandidatesPreserveEvidence
<1>1. ASSUME NEW c \in Replicas, role[c] = "LeaderCandidate", phase[c] = "collect",
            c \in Reporters(c), Quorum(Reporters(c)),
            NEW p \in Latest(ReportedProposals(c)), NEW f \in commitHistory, f.epoch < term[c]
      PROVE f.entry \in Recovered(c, p)
    <2>1. f.epoch \in Terms /\ f.epoch \in Nat /\ f.entry \in IssuedEntries /\ MayChoose(f.epoch, f.entry)
        BY SMT, EvidenceIsPossible, <1>1 DEF Terms
    <2>2. term \in [Replicas -> Nat] /\ \A q \in proposals : q \in ProposalRecords
        BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
    <2> QED BY RecoveryResultPreservesPossible, <1>1, <2>1, <2>2
<1> QED BY <1>1 DEF RecoveryCandidatesPreserveEvidence

THEOREM CandidateWithAppliedEvidenceImpliesStateMachineSafety ==
    (ProofInvariant /\ CommitEvidenceSound /\ AppliedEvidence) => StateMachineSafety
BY SMT, CandidateImpliesEvidenceAgreement DEF AppliedEvidence, CommitEvidenceAgreement, StateMachineSafety
=============================================================================
