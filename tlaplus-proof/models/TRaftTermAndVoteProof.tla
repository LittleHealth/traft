------------------------ MODULE TRaftTermAndVoteProof ------------------------
EXTENDS TRaftProofState, TRaftControlTemporal, TRaftStepProof, TRaftRecoveryProof

THEOREM StrongLayersImplyTermAndVoteFacts ==
    (ElectionInvariant /\ ControlInvariant) => TermAndVoteFacts
<1>1. ASSUME ElectionInvariant, ControlInvariant
      PROVE TermAndVoteFacts
    <2>1. \A w \in winners :
              BallotVoters(voteMessages, w.epoch, w.node) =
              {v.sender : v \in {a \in voteMessages :
                   a.epoch = w.epoch /\ a.receiver = w.node}}
        BY SMT, <1>1 DEF ElectionInvariant, ElectionBallotFacts, BallotVoters
    <2> QED BY ONLY ZenonT(10), <1>1, <2>1 DEF TermAndVoteFacts, ElectionInvariant,
        ElectionBallotFacts, ElectionWinnerFacts, BallotCertificates,
        ControlInvariant, ProposalProvenance, OwnedEpochs, ReportProvenance
<1> QED BY <1>1

THEOREM ProtocolTermAndVoteFacts == Spec => []TermAndVoteFacts
BY PTL, StrongLayersImplyTermAndVoteFacts, ElectionInvariantAlways, ControlInvariantAlways

THEOREM CandidateStepHasMonotonicFacts ==
    ASSUME ProofInvariant, ProtocolNext
    PROVE StepFacts
<1>1. StepTypes /\ Terms \subseteq Nat
      /\ (\A p \in proposals : p.prefix \subseteq Entries /\ p.first \in Entries)
      /\ (\A r \in Replicas : retained[r] \subseteq proposals)
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, StepTypes, Terms
<1>2. \A c \in Replicas : ReportedProposals(c) \subseteq proposals
    BY ReportedProposalsAreActual
<1> QED BY EveryProtocolStepHasFacts, <1>1, <1>2
=============================================================================
