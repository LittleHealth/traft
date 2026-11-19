------------------------- MODULE TRaftOfferDiagnostic ------------------------
EXTENDS TRaftPaperScenarios, TRaftProofState

\* Synthetic-channel induction diagnostic. The bootstrap actions are real,
\* but Init is deliberately replaced with a state containing a forged offer.
\* This is not a reachable counterexample to the protocol.
BadEntry == Entry(2, 1, 0, NoValue, "data", 0)
BadOffer == [owner |-> A, epoch |-> 1, entry |-> BadEntry, committed |-> 0]
EmptyOfferInitial == INSTANCE TRaftCore WITH offers <- {}
OfferDiagnosticInit == EmptyOfferInitial!Init /\ offers = {BadOffer}
                       /\ GhostInit /\ pc = 0
OfferDiagnosticNext ==
    /\ IF pc < 21 THEN recoveryStep
          ELSE IF pc = 21 THEN ReceiveEntry(B, BadOffer)
          ELSE UNCHANGED protocolVars
    /\ Observe /\ GhostNext
    /\ pc' = IF pc < 22 THEN pc + 1 ELSE pc
OfferDiagnosticVars == <<proofVars, pc>>
OfferDiagnosticSpec == OfferDiagnosticInit /\ [][OfferDiagnosticNext]_OfferDiagnosticVars
PreMessageCandidate == Safety /\ PreProvenanceInvariant
OfferStrengtheningExcludesDiagnostic == ~ProofInvariant
=============================================================================
