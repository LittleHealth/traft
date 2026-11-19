------------------------ MODULE TRaftInvariantDefinitions --------------------
EXTENDS TRaftProofState

ASSUME FormalFaultsDisabled ==
    /\ ~MutDropPending /\ ~MutSkipRecoveryUnion /\ ~MutEarlyPublish
    /\ ~MutNoCommitQuorum /\ ~MutSkipBoundaryCommit
USE FormalFaultsDisabled DEF FormalFaultsDisabled

Inv == Safety /\ ProofInvariant

=============================================================================
