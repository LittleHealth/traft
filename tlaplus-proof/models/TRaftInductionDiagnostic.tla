---------------------- MODULE TRaftInductionDiagnostic -----------------------
EXTENDS TRaftProofState
CONSTANT A

\* COUNTERMODEL TO THE CANDIDATE INDUCTION LEMMA, NOT A PROTOCOL EXECUTION
\* FROM Init. Only the initial vote-request channel is deliberately synthetic.
\* This demonstrates why finite reachable-state tests do not prove induction.
EmptyRequestInitial == INSTANCE TRaftCore WITH voteRequests <- {}
BadRequest == [candidate |-> NoNode, epoch |-> 0, entries |-> {}]
DiagnosticInit == EmptyRequestInitial!Init /\ GhostInit
                  /\ voteRequests = {BadRequest}
DiagnosticNext == GrantVote(A, BadRequest) /\ Observe /\ GhostNext
DiagnosticSpec == DiagnosticInit /\ [][DiagnosticNext]_proofVars
CandidateInvariant == Safety /\ RecoveryInvariant
StrengthenedInvariantExcludesDiagnostic == ~ProofInvariant
=============================================================================
