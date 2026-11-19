------------------------- MODULE TRaftClientUnbounded ------------------------
EXTENDS Integers, FiniteSets
CONSTANTS Replicas, MaxPartitionSize, Absent, NoValue,
          Clients, Series, Times, Values, Missing

AllCommands == {q \in [id : Clients \X (Nat \ {0}),
                       op : {"Put", "Delete", "Get"},
                       key : Series \X Times, value : Values \cup {Missing}] :
                    IF q.op = "Put" THEN q.value \in Values ELSE q.value = Missing}

VARIABLES term, vote, alive, role, phase, formal, stored, retained,
          current, reports, voteInbox, ackInbox, knownCommitted, applied,
          voteRequests, voteMessages, recoveryRequests, reportMessages,
          offers, proposals, ackMessages, confirmations, commitMessages,
          winners, leaderViews, commitHistory, partitionHistory,
          appendOnlyOK, appliedPartitionHistory, applicationOrderOK, entryContexts,
          calls, nextSequence, machine, cache, replyMessages, returned, history,
          witness, abstractMachine, abstractAnswers

INSTANCE TRaftClients WITH DataValues <- AllCommands,
          MaxTerm <- (-1), MaxIndex <- (-1),
          MaxPartition <- (-1), MaxSequence <- (-1),
          MutDropPending <- FALSE, MutSkipRecoveryUnion <- FALSE,
          MutEarlyPublish <- FALSE, MutNoCommitQuorum <- FALSE,
          MutSkipBoundaryCommit <- FALSE, MutEarlyReply <- FALSE,
          MutReadWithoutBarrier <- FALSE, MutLoseDedup <- FALSE
\* These are the unchanged constant-parameter conditions of the core/client
\* modules; no safety or witness property is assumed.
ASSUME UnboundedClientParameters ==
    ParameterAssumptions /\ SentinelSeparation /\ ClientParameters
=============================================================================
