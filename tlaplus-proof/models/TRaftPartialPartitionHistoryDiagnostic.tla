--------------------- MODULE TRaftPartialPartitionHistoryDiagnostic --------------------
EXTENDS TRaftOfferDiagnostic

\* Synthetic predecessor: a committed history record contains only part of
\* its actually closed partition. Individual entry evidence is insufficient.
BoundaryBase == Entry(1, 1, 0, NoValue, "noop", 0)
BoundaryEarlier == Entry(2, 1, 0, V1, "data", 0)
BadBoundary == Entry(3, 1, 1, V2, "data", 2)
BoundaryLog == {BoundaryBase, BoundaryEarlier, BadBoundary}
PartialPartitionHistoryDiagnosticInit ==
/\ commitMessages = {[owner |-> A, epoch |-> 1, entry |-> BoundaryBase],
    [owner |-> A, epoch |-> 1, entry |-> BoundaryEarlier]}
/\ voteMessages = { [epoch |-> 1, sender |-> A, receiver |-> A],
  [epoch |-> 1, sender |-> B, receiver |-> A] }
/\ applicationOrderOK = TRUE
/\ vote = (A :> A @@ B :> A @@ C :> "NoNode")
/\ reportMessages = { [epoch |-> 1, sender |-> A, receiver |-> A, entries |-> {}, pending |-> {}],
  [ epoch |-> 1,
    sender |-> B,
    receiver |-> A,
    entries |-> {},
    pending |-> {} ] }
/\ applied = (A :> {} @@ B :> {} @@ C :> {})
/\ leaderViews = {[node |-> A, epoch |-> 1, entries |-> {BoundaryBase}],
                 [node |-> A, epoch |-> 1, entries |-> BoundaryLog]}
/\ canonical = [t \in Terms |-> IF t = 1 THEN BoundaryLog ELSE {}]
/\ voteInbox = ( A :>
      { [epoch |-> 1, sender |-> A, receiver |-> A],
        [epoch |-> 1, sender |-> B, receiver |-> A] } @@
  B :> {} @@
  C :> {} )
/\ formal = [r \in Replicas |-> IF r = A THEN BoundaryLog ELSE IF r = B THEN {BoundaryBase, BoundaryEarlier} ELSE {}]
/\ entryContexts = {[entry |-> BoundaryBase, prefix |-> {}],
    [entry |-> BoundaryEarlier, prefix |-> {}],
    [entry |-> BadBoundary, prefix |-> {BoundaryBase, BoundaryEarlier}]}
/\ voteRequests = {[epoch |-> 1, candidate |-> A, entries |-> {}]}
/\ role = (A :> "Leader" @@ B :> "Follower" @@ C :> "Follower")
/\ commitHistory = {[epoch |-> 1, entry |-> BoundaryBase], [epoch |-> 1, entry |-> BoundaryEarlier]}
/\ appliedPartitionHistory = {}
/\ stored = [r \in Replicas |-> IF r = A THEN BoundaryLog ELSE IF r = B THEN {BoundaryBase, BoundaryEarlier} ELSE {}]
/\ winners = {[epoch |-> 1, node |-> A]}
/\ phase = (A :> "serve" @@ B :> "idle" @@ C :> "idle")
/\ offers = {}
/\ pc = 21
/\ appendOnlyOK = TRUE
/\ knownCommitted = [r \in Replicas |-> IF r = A THEN {BoundaryBase, BoundaryEarlier} ELSE {}]
/\ retained = ( A :>
      { [ owner |-> A,
          epoch |-> 1,
          first |->
              [ term |-> 1,
                index |-> 1,
                part |-> 0,
                value |-> "NoValue",
                kind |-> "noop",
                prevSize |-> 0 ],
          recovering |-> TRUE,
          prefix |-> {} ] } @@
  B :>
      { [ owner |-> A,
          epoch |-> 1,
          first |->
              [ term |-> 1,
                index |-> 1,
                part |-> 0,
                value |-> "NoValue",
                kind |-> "noop",
                prevSize |-> 0 ],
          recovering |-> TRUE,
          prefix |-> {} ] } @@
  C :> {} )
/\ partitionHistory = {[epoch |-> 1, part |-> 0, entries |-> {BoundaryBase}]}
/\ reports = ( A :>
      ( A :>
            [ epoch |-> 1,
              sender |-> A,
              receiver |-> A,
              entries |-> {},
              pending |-> {} ] @@
        B :>
            [ epoch |-> 1,
              sender |-> B,
              receiver |-> A,
              entries |-> {},
              pending |-> {} ] @@
        C :> Absent ) @@
  B :> (A :> Absent @@ B :> Absent @@ C :> Absent) @@
  C :> (A :> Absent @@ B :> Absent @@ C :> Absent) )
/\ confirmations = { [ owner |-> A,
    epoch |-> 1,
    first |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ],
    recovering |-> TRUE,
    prefix |-> {} ] }
/\ term = (A :> 1 @@ B :> 1 @@ C :> 0)
/\ proposals = { [ owner |-> A,
    epoch |-> 1,
    first |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ],
    recovering |-> TRUE,
    prefix |-> {} ] }
/\ ackMessages = {Ack(A, A, 1, BoundaryBase, {BoundaryBase}), Ack(B, A, 1, BoundaryBase, {BoundaryBase}),
    Ack(A, A, 1, BoundaryEarlier, {BoundaryEarlier}), Ack(B, A, 1, BoundaryEarlier, {BoundaryEarlier})}
/\ recoveryRequests = {[owner |-> A, epoch |-> 1]}
/\ ackInbox = [r \in Replicas |-> IF r = A THEN ackMessages ELSE {}]
/\ current = ( A :>
      [ owner |-> A,
        epoch |-> 1,
        first |->
            [ term |-> 1,
              index |-> 1,
              part |-> 0,
              value |-> "NoValue",
              kind |-> "noop",
              prevSize |-> 0 ],
        recovering |-> TRUE,
        prefix |-> {} ] @@
  B :> Absent @@
  C :> Absent )
/\ alive = (A :> TRUE @@ B :> TRUE @@ C :> TRUE)

PartialPartitionHistoryDiagnosticNext == pc = 21 /\ SendEntry(A, BadBoundary) /\ Observe /\ GhostNext /\ pc' = 22
PartialPartitionHistoryDiagnosticSpec == PartialPartitionHistoryDiagnosticInit /\ [][PartialPartitionHistoryDiagnosticNext]_OfferDiagnosticVars
PartialHistoryCandidate == Safety /\ PreClosedHistoryInvariant
ClosedHistoryStrengtheningExcludesPredecessor == pc = 21 => ~ProofInvariant
=============================================================================
