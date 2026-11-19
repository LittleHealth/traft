--------------------- MODULE TRaftProposalIdentityProof ----------------------
EXTENDS TRaftControlTemporal

THEOREM OnlyRecoveryCreatesProposal ==
    ProtocolNext =>
       (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
       \/ UNCHANGED proposals
<1>1. \A c : (StartElection(c) \/ WinElection(c) \/ ConfirmProposal(c)
              \/ Activate(c) \/ Crash(c)) => UNCHANGED proposals
    BY SMT DEF StartElection, WinElection, ConfirmProposal, Activate, Crash
<1>2. \A r, t : AdoptTerm(r, t) => UNCHANGED proposals
    BY SMT DEF AdoptTerm
<1>3. \A r, req : MakeReport(r, req) => UNCHANGED proposals
    BY SMT DEF MakeReport
<1>4. \A c, m : DeliverReport(c, m) => UNCHANGED proposals
    BY SMT DEF DeliverReport
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, ProtocolControlProjection
    DEF ControlChangingNext, ControlCoreVars

THEOREM BuildRecoveryPreservesProposalIdentity ==
    ASSUME ControlInvariant, ElectionInvariant, ElectionSafety, UniqueProposalEpoch,
           NEW c \in Replicas, NEW p, BuildRecovery(c, p)
    PROVE UniqueProposalEpoch'
<1>00. role[c] = "LeaderCandidate" /\ phase[c] = "collect"
    BY DEF BuildRecovery
<1>01. [node |-> c, epoch |-> term[c]] \in winners
    BY SMT, <1>00 DEF ElectionInvariant, ElectionWinnerFacts
<1>1. ~\E q \in proposals : q.epoch = term[c]
    BY RecoveryCreatorHasFreshEpoch, <1>00, <1>01
<1>2. \A q \in proposals' \ proposals : q.epoch = term[c]
    BY SMT DEF BuildRecovery, Proposal
<1>3. \A q, s \in proposals' \ proposals : q = s
    BY ZenonT(10) DEF BuildRecovery
<1> QED BY SMT, <1>1, <1>2, <1>3 DEF UniqueProposalEpoch

THEOREM ProposalIdentityInductiveStep ==
    ASSUME ControlInvariant, ElectionInvariant, ElectionSafety, UniqueProposalEpoch,
           [Next]_vars
    PROVE UniqueProposalEpoch'
<1>1. (\E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p))
       \/ UNCHANGED proposals
    BY SMT, OnlyRecoveryCreatesProposal DEF Next, vars, protocolVars, observerVars
<1> QED BY SMT, <1>1, BuildRecoveryPreservesProposalIdentity DEF UniqueProposalEpoch

THEOREM ProtocolUniqueProposalEpoch == Spec => []UniqueProposalEpoch
<1>1. Spec => [](ElectionInvariant /\ ElectionSafety /\ ControlInvariant)
    BY PTL, ElectionInvariantAlways, ProtocolElectionSafety, ControlInvariantAlways
<1>2. Init => UniqueProposalEpoch
    BY SMT DEF Init, UniqueProposalEpoch
<1> QED BY PTL, <1>1, <1>2, ProposalIdentityInductiveStep DEF Spec
=============================================================================
