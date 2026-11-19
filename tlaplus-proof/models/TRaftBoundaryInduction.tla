----------------------- MODULE TRaftBoundaryInduction -----------------------
EXTENDS TRaftInvariantDefinitions, TRaftBoundaryCountActions
USE FormalFaultsDisabled DEF FormalFaultsDisabled

THEOREM EntryBoundaryInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE EntryBoundaryCounts'
<1>1. ProofInvariant /\ EntryBoundaryCounts /\ ProtocolNext /\ Observe
    BY DEF Inv, ProofInvariant, ProofNext, Next
<1>2. LeaderBoundaryFacts(role', formal') /\ ProposalBoundaryCounts(proposals')
    BY SMT, <1>1, BoundaryCountActionProjection, BoundaryCountsFrame,
       BuildRecoveryBoundaryCounts, CreateEntryBoundaryCounts, CreateSuccessorBoundaryCounts,
       ReceiveBoundaryCounts, ConfirmBoundaryCounts, LearnConfirmationBoundaryCounts
       DEF BoundaryCountChanges
<1> QED BY PostContextsWithCounts, <1>1, <1>2
=============================================================================
