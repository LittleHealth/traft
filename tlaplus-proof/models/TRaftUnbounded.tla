--------------------------- MODULE TRaftUnbounded ---------------------------
EXTENDS Integers, FiniteSets

\* The selector -1 is provably outside Nat; it selects the unbounded branch.
\* Infinite identifier domains; each concrete log/message set is finite initially
\* and each protocol step adds only finitely many entries. No mutation switches.
CONSTANTS Replicas, DataValues, MaxPartitionSize, Absent, NoValue

VARIABLES term, vote, alive, role, phase, formal, stored, retained,
          current, reports, voteInbox, ackInbox, knownCommitted, applied,
          voteRequests, voteMessages, recoveryRequests, reportMessages,
          offers, proposals, ackMessages, confirmations, commitMessages,
          winners, leaderViews, commitHistory, partitionHistory,
          appendOnlyOK, appliedPartitionHistory, applicationOrderOK, entryContexts

INSTANCE TRaftCore WITH MaxTerm <- (-1), MaxIndex <- (-1),
                         MaxPartition <- (-1),
                         MutDropPending <- FALSE, MutSkipRecoveryUnion <- FALSE,
                         MutEarlyPublish <- FALSE, MutNoCommitQuorum <- FALSE,
                         MutSkipBoundaryCommit <- FALSE
\* INSTANCE exports the instantiated definitions, not new outer assumptions.
\* State exactly the core's constant-parameter preconditions at this entry.
ASSUME UnboundedParameters == ParameterAssumptions /\ SentinelSeparation
=============================================================================
