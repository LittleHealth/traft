---------------- MODULE TRaftUnboundedSafetyDefinitions ----------------
EXTENDS TRaftInvariantDefinitions, TLAPS

\* These are the same selectors and disabled faults of the original
\* unbounded specialization. No invariant or safety condition is assumed.
\* The definition identities do not use the protocol theorem. The final
\* TRaftUnboundedSafetyProof imports that proof separately before transport.
ASSUME UnboundedSelectors ==
    MaxTerm = (-1) /\ MaxIndex = (-1) /\ MaxPartition = (-1)
USE UnboundedSelectors, FormalFaultsDisabled, ParameterAssumptions, SentinelSeparation
    DEF UnboundedSelectors, FormalFaultsDisabled, ParameterAssumptions, SentinelSeparation

UnboundedCore == INSTANCE TRaftUnbounded

THEOREM UnboundedConstantSelections ==
    /\ MaxTerm = (-1) /\ MaxIndex = (-1) /\ MaxPartition = (-1)
    /\ MutDropPending = FALSE /\ MutSkipRecoveryUnion = FALSE
    /\ MutEarlyPublish = FALSE /\ MutNoCommitQuorum = FALSE
    /\ MutSkipBoundaryCommit = FALSE
BY ONLY SMT, UnboundedSelectors, FormalFaultsDisabled, ParameterAssumptions
   DEF UnboundedSelectors, FormalFaultsDisabled, ParameterAssumptions
=============================================================================
