--------------------- MODULE TRaftRecoveryHistoryDiagnostic ------------------
EXTENDS TRaftOfferDiagnostic

\* A synthetic candidate state, not a behavior from Init. A closed-partition
\* history refers to an unconfirmed recovery boundary. A later candidate
\* has a different, confirmed recovery result and can legally Activate.
RHBase == Entry(1, 1, 0, NoValue, "noop", 0)
RHLeft == Entry(2, 1, 0, V1, "data", 0)
RHExtra == Entry(3, 1, 0, V2, "data", 0)
RHFirst2 == Entry(3, 2, 1, NoValue, "noop", 2)
RHFirst3 == Entry(4, 3, 1, NoValue, "noop", 3)
RHP1 == Proposal(A, 1, {}, RHBase, TRUE)
RHP2 == Proposal(B, 2, {RHBase, RHLeft}, RHFirst2, TRUE)
RHP3 == Proposal(C, 3, {RHBase, RHLeft, RHExtra}, RHFirst3, TRUE)
RHOldLog == {RHBase, RHLeft, RHExtra}

RecoveryHistoryDiagnosticInit ==
    /\ term = [r \in Replicas |-> 3]
    /\ vote = [r \in Replicas |-> IF r = B THEN NoNode ELSE C]
    /\ alive = [r \in Replicas |-> TRUE]
    /\ role = [r \in Replicas |-> IF r = C THEN "LeaderCandidate" ELSE "Follower"]
    /\ phase = [r \in Replicas |-> IF r = C THEN "commit" ELSE "idle"]
    /\ current = [r \in Replicas |-> IF r = C THEN RHP3 ELSE NoProposal]
    /\ formal = [r \in Replicas |-> IF r = A THEN Result(RHP2) ELSE Result(RHP3)]
    /\ stored = formal
    /\ retained = [r \in Replicas |-> IF r = A THEN {RHP1, RHP2}
                            ELSE IF r = B THEN {RHP1, RHP3} ELSE {RHP3}]
    /\ proposals = {RHP1, RHP2, RHP3}
    /\ confirmations = {RHP1, RHP3}
    /\ ackMessages = {Ack(A, A, 1, RHBase, Result(RHP1)), Ack(B, A, 1, RHBase, Result(RHP1)),
          Ack(A, A, 1, RHLeft, {RHLeft}), Ack(B, A, 1, RHLeft, {RHLeft}),
          Ack(B, C, 3, RHFirst3, Result(RHP3)), Ack(C, C, 3, RHFirst3, Result(RHP3))}
    /\ ackInbox = [r \in Replicas |-> IF r = C THEN
          {Ack(B, C, 3, RHFirst3, Result(RHP3)), Ack(C, C, 3, RHFirst3, Result(RHP3))} ELSE {}]
    /\ commitHistory = Evidence(ackMessages)
    /\ knownCommitted = [r \in Replicas |-> IF r = C THEN Result(RHP3) ELSE {}]
    /\ commitMessages = {} /\ offers = {}
    /\ applied = [r \in Replicas |-> {}] /\ appliedPartitionHistory = {}
    /\ reports = [r \in Replicas |-> EmptyReports] /\ reportMessages = {}
    /\ voteInbox = [r \in Replicas |-> {}]
    /\ voteRequests = {[candidate |-> A, epoch |-> 1, entries |-> {}],
          [candidate |-> B, epoch |-> 2, entries |-> {}],
          [candidate |-> C, epoch |-> 3, entries |-> {}]}
    /\ voteMessages = {[sender |-> A, receiver |-> A, epoch |-> 1],
          [sender |-> B, receiver |-> A, epoch |-> 1],
          [sender |-> B, receiver |-> B, epoch |-> 2],
          [sender |-> C, receiver |-> B, epoch |-> 2],
          [sender |-> A, receiver |-> C, epoch |-> 3],
          [sender |-> C, receiver |-> C, epoch |-> 3]}
    /\ recoveryRequests = {[owner |-> A, epoch |-> 1], [owner |-> B, epoch |-> 2], [owner |-> C, epoch |-> 3]}
    /\ winners = {[node |-> A, epoch |-> 1], [node |-> B, epoch |-> 2], [node |-> C, epoch |-> 3]}
    /\ leaderViews = {[node |-> A, epoch |-> 1, entries |-> RHOldLog]}
    /\ canonical = [t \in Terms |-> CASE t = 1 -> RHOldLog [] t = 2 -> Result(RHP2)
                                    [] t = 3 -> Result(RHP3) [] OTHER -> {}]
    /\ entryContexts = {[entry |-> RHBase, prefix |-> {}], [entry |-> RHLeft, prefix |-> {}],
          [entry |-> RHExtra, prefix |-> {}], [entry |-> RHFirst2, prefix |-> RHP2.prefix],
          [entry |-> RHFirst3, prefix |-> RHP3.prefix]}
    /\ partitionHistory = {[epoch |-> 2, part |-> 0, entries |-> {RHBase, RHLeft}]}
    /\ appendOnlyOK = TRUE /\ applicationOrderOK = TRUE /\ pc = 21

RecoveryHistoryDiagnosticNext == pc = 21 /\ Activate(C) /\ Observe /\ GhostNext /\ pc' = 22
RecoveryHistoryDiagnosticSpec == RecoveryHistoryDiagnosticInit /\ [][RecoveryHistoryDiagnosticNext]_OfferDiagnosticVars
RecoveryHistoryCandidate == Safety /\ PreCertifiedHistoryInvariant
RecoveryHistoryPredecessorSatisfiesCandidate == pc = 21 => RecoveryHistoryCandidate
RecoveryHistoryExcludedByCurrentCandidate == pc = 21 => ~(Safety /\ ProofInvariant)
=============================================================================
