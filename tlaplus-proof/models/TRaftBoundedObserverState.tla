----------------------- MODULE TRaftBoundedObserverState ---------------------
EXTENDS TRaftBoundedObserverInputs

MappedCore == INSTANCE TRaftCore WITH MaxTerm <- (-1), MaxIndex <- (-1), MaxPartition <- (-1),
                                      partitionHistory <- EpochClosure(partitionHistory)

ExpandedObservation ==
    /\ winners' = winners \cup PresentWinners'
    /\ leaderViews' = leaderViews \cup PresentViews'
    /\ entryContexts' = entryContexts \cup PresentContexts'
    /\ commitHistory' = commitHistory \cup Infinite!Evidence(ackMessages')
    /\ EpochClosure(partitionHistory') = EpochClosure(partitionHistory) \cup
          CertifiedClosed(UnboundedClosed', commitHistory', Nat \ {0})
    /\ appliedPartitionHistory' = appliedPartitionHistory \cup PresentAppliedPartitions'
    /\ ObservationBooleans

ObserverMappingContext ==
    /\ term \in [Replicas -> Terms]
    /\ formal \in [Replicas -> SUBSET Entries]
    /\ CommitEvidenceSound
    /\ \A a \in ackMessages : a.epoch \in Terms \ {0}
=============================================================================
