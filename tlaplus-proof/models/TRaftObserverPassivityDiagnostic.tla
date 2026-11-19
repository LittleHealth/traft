------------------ MODULE TRaftObserverPassivityDiagnostic ------------------
EXTENDS TRaftPaper
CONSTANT ProbeReplica
VARIABLE probeStep
ProbeVars == <<vars, probeStep>>
ProbeEntry == Entry(1, 1, 0, NoValue, "noop", 0)
ProbeInit == Init /\ probeStep = 0
\* Deliberately bypass ApplyEntry. This is a test of the observer, NOT a
\* protocol execution. Observe must record the violation and allow the step.
ProbeNext ==
    /\ probeStep = 0 /\ probeStep' = 1
    /\ applied' = [applied EXCEPT ![ProbeReplica] = {ProbeEntry}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   voteRequests, voteMessages, recoveryRequests, reportMessages,
                   offers, proposals, ackMessages, confirmations, commitMessages>>
    /\ Observe
ProbeSpec == ProbeInit /\ [][ProbeNext]_ProbeVars
NoRecordedOrderViolation == applicationOrderOK
=============================================================================
