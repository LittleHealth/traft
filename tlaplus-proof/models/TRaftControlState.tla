-------------------------- MODULE TRaftControlState --------------------------
EXTENDS TRaftElectionState

\* Control/message provenance used only in proofs. All state is protocol state
\* or an existing observer; no protocol transition consults this predicate.
ControlCoreVars == <<term, role, phase, current, proposals, recoveryRequests,
                     reportMessages, reports>>
ControlVars == <<ControlCoreVars, winners>>

ControlShape ==
    /\ phase \in [Replicas -> Phases]
    /\ current \in [Replicas -> proposals \cup {NoProposal}]
    /\ reports \in [Replicas -> [Replicas -> reportMessages \cup {NoReport}]]
    /\ \A r \in Replicas :
         /\ (role[r] = "Leader") <=> (phase[r] = "serve")
         /\ (role[r] = "LeaderCandidate") <=> (phase[r] \in {"collect", "sync", "commit"})
         /\ phase[r] \in {"idle", "collect"} => current[r] = NoProposal
         /\ phase[r] \in {"sync", "commit", "serve"} =>
              /\ current[r] \in proposals
              /\ current[r].owner = r /\ current[r].epoch = term[r]

OwnedEpochs(S, T, W) == \A p \in S :
    /\ p.owner \in Replicas /\ p.epoch \in Terms \ {0}
    /\ p.epoch <= T[p.owner]
    /\ [node |-> p.owner, epoch |-> p.epoch] \in W

ProposalProvenance == OwnedEpochs(proposals, term, winners)

UnusedProposalEpoch == \A r \in Replicas :
    role[r] = "Candidate" \/ phase[r] = "collect" =>
        ~\E p \in proposals : p.owner = r /\ p.epoch = term[r]

RecoveryRequestProvenance == OwnedEpochs(recoveryRequests, term, winners)

ReportProvenance == \A m \in reportMessages :
    /\ m.sender \in Replicas /\ m.receiver \in Replicas
    /\ m.epoch \in Terms \ {0} /\ m.epoch <= term[m.sender]
    /\ \E req \in recoveryRequests : req.owner = m.receiver /\ req.epoch = m.epoch

CollectedReportProvenance == \A c \in Replicas : \A r \in Reporters(c) :
    /\ reports[c][r] \in reportMessages
    /\ reports[c][r].sender = r /\ reports[c][r].receiver = c
    /\ reports[c][r].epoch = term[c]

ControlInvariant == /\ ControlShape /\ ProposalProvenance /\ UnusedProposalEpoch
                    /\ RecoveryRequestProvenance /\ ReportProvenance
                    /\ CollectedReportProvenance
ControlChangingNext ==
    \/ \E c \in Replicas : StartElection(c) \/ WinElection(c) \/ ConfirmProposal(c) \/ Activate(c) \/ Crash(c)
    \/ \E r \in Replicas, t \in Terms : AdoptTerm(r, t)
    \/ \E r \in Replicas, req \in recoveryRequests : MakeReport(r, req)
    \/ \E c \in Replicas, m \in reportMessages : DeliverReport(c, m)
    \/ \E c \in Replicas : \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} : BuildRecovery(c, p)

UniqueProposalEpoch == \A p, q \in proposals : p.epoch = q.epoch => p = q
=============================================================================
