--------------------- MODULE TRaftNoopSelfAckDiagnostic -----------------------
EXTENDS TRaftProofScenarios

\* This trace starts at protocol Init. A normal boundary no-op is not a
\* recovery proposal; its owner's singleton ACK need not cover its prefix.
NoopSelfAckStep ==
    IF pc < 20 THEN recoveryStep
    ELSE CASE pc = 20 -> CreateEntry(A, V1)
           [] pc = 21 -> CreateSuccessor(A, NoValue, "noop")
           [] pc = 22 -> SendEntry(A, E(1, 3))
           [] pc = 23 -> AckEntry(A, M(1, 3, 1))
NoopSelfAckNext == /\ pc < 24 /\ NoopSelfAckStep /\ Observe /\ GhostNext
                  /\ pc' = pc + 1
NoopSelfAckSpec == ProofScenarioInit /\ [][NoopSelfAckNext]_proofScenarioVars
NoopSelfAckProjectsToCore == [][Next]_vars
NoopSelfAckLegacyConstraint == \A a \in ackMessages, ctx \in entryContexts :
    (ctx.entry \in a.contents /\ (a.sender # a.receiver \/ a.target.kind = "noop")) =>
        \A x \in ctx.prefix : x \in a.contents \/ KnownBy(commitHistory, a.epoch, x)
NoopSelfAckPredecessorsSatisfyCandidate == pc < 24 => Safety /\ ProofInvariant
NoopSelfAckEndpoint == pc = 24 =>
    /\ DA(A, A, 1, 3) \in ackMessages
    /\ E(1, 2) \notin EvidenceEntries /\ E(1, 3) \notin EvidenceEntries
=============================================================================
