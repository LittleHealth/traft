-------------------- MODULE TRaftUnboundedClientDefinitions --------------------
EXTENDS TRaftSharedClientSpecification, TRaftInvariantDefinitions, TLAPS

ASSUME UnboundedClientSelectors ==
    /\ MaxTerm = (-1) /\ MaxIndex = (-1) /\ MaxPartition = (-1) /\ MaxSequence = (-1)
    /\ ~MutEarlyReply /\ ~MutReadWithoutBarrier /\ ~MutLoseDedup
USE UnboundedClientSelectors, FormalFaultsDisabled, ParameterAssumptions,
    SentinelSeparation, ClientParameters
    DEF UnboundedClientSelectors, FormalFaultsDisabled, ParameterAssumptions,
        SentinelSeparation, ClientParameters

AllCommands == {q \in [id : Clients \X (Nat \ {0}),
                       op : {"Put", "Delete", "Get"},
                       key : Series \X Times, value : Values \cup {Missing}] :
                    IF q.op = "Put" THEN q.value \in Values ELSE q.value = Missing}

UnboundedClient == INSTANCE TRaftSharedClientSpecification WITH DataValues <- AllCommands,
          MaxTerm <- (-1), MaxIndex <- (-1), MaxPartition <- (-1), MaxSequence <- (-1),
          MutDropPending <- FALSE, MutSkipRecoveryUnion <- FALSE,
          MutEarlyPublish <- FALSE, MutNoCommitQuorum <- FALSE,
          MutSkipBoundaryCommit <- FALSE, MutEarlyReply <- FALSE,
          MutReadWithoutBarrier <- FALSE, MutLoseDedup <- FALSE

THEOREM UnboundedClientDomains ==
    /\ Terms = Nat /\ Indices = Nat \ {0} /\ Partitions = Nat
    /\ RequestIds = Clients \X (Nat \ {0}) /\ DataValues = AllCommands
BY SMT DEF Terms, Indices, Partitions, RequestIds, SeqDomain, ClientCommands,
           AllCommands, Keys


THEOREM UnboundedClientConstantSelections ==
    /\ MaxTerm = (-1) /\ MaxIndex = (-1) /\ MaxPartition = (-1) /\ MaxSequence = (-1)
    /\ MutDropPending = FALSE /\ MutSkipRecoveryUnion = FALSE
    /\ MutEarlyPublish = FALSE /\ MutNoCommitQuorum = FALSE /\ MutSkipBoundaryCommit = FALSE
    /\ MutEarlyReply = FALSE /\ MutReadWithoutBarrier = FALSE /\ MutLoseDedup = FALSE
BY ONLY SMT, UnboundedClientSelectors, FormalFaultsDisabled,
   ParameterAssumptions, ClientParameters
   DEF UnboundedClientSelectors, FormalFaultsDisabled, ParameterAssumptions, ClientParameters
=============================================================================
