--------------------- MODULE TRaftAppliedHistoryDiagnostic --------------------
EXTENDS TRaftOfferDiagnostic

\* Synthetic predecessor with a fabricated applied-partition history record.
\* The protocol state is coherent; Inv lacks the record's origin constraint.
BoundaryBase == Entry(1, 1, 0, NoValue, "noop", 0)
BoundaryEarlier == Entry(2, 1, 0, V1, "data", 0)
BadBoundary == Entry(2, 1, 1, V2, "data", 1)
BoundaryLog == {BoundaryBase, BadBoundary}
AppliedHistoryDiagnosticInit ==
/\ commitMessages = { [ owner |-> A,
    epoch |-> 1,
    entry |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] ] }
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
/\ formal = [r \in Replicas |-> IF r = A THEN BoundaryLog ELSE IF r = B THEN {BoundaryBase} ELSE {}]
/\ entryContexts = {[entry |-> BoundaryBase, prefix |-> {}],
                   [entry |-> BadBoundary, prefix |-> {BoundaryBase}]}
/\ voteRequests = {[epoch |-> 1, candidate |-> A, entries |-> {}]}
/\ role = (A :> "Leader" @@ B :> "Follower" @@ C :> "Follower")
/\ commitHistory = { [ epoch |-> 1,
    entry |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] ] }
/\ appliedPartitionHistory = {[node |-> B, part |-> 0, entries |-> {BoundaryEarlier}]}
/\ stored = [r \in Replicas |-> IF r = A THEN BoundaryLog ELSE IF r = B THEN {BoundaryBase} ELSE {}]
/\ winners = {[epoch |-> 1, node |-> A]}
/\ phase = (A :> "serve" @@ B :> "idle" @@ C :> "idle")
/\ offers = {}
/\ pc = 21
/\ appendOnlyOK = TRUE
/\ knownCommitted = ( A :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  B :> {} @@
  C :> {} )
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
/\ partitionHistory = {}
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
/\ ackMessages = { [ epoch |-> 1,
    sender |-> A,
    receiver |-> A,
    contents |->
        { [ term |-> 1,
            index |-> 1,
            part |-> 0,
            value |-> "NoValue",
            kind |-> "noop",
            prevSize |-> 0 ] },
    target |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] ],
  [ epoch |-> 1,
    sender |-> B,
    receiver |-> A,
    contents |->
        { [ term |-> 1,
            index |-> 1,
            part |-> 0,
            value |-> "NoValue",
            kind |-> "noop",
            prevSize |-> 0 ] },
    target |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] ] }
/\ recoveryRequests = {[owner |-> A, epoch |-> 1]}
/\ ackInbox = ( A :>
      { [ epoch |-> 1,
          sender |-> A,
          receiver |-> A,
          contents |->
              { [ term |-> 1,
                  index |-> 1,
                  part |-> 0,
                  value |-> "NoValue",
                  kind |-> "noop",
                  prevSize |-> 0 ] },
          target |->
              [ term |-> 1,
                index |-> 1,
                part |-> 0,
                value |-> "NoValue",
                kind |-> "noop",
                prevSize |-> 0 ] ],
        [ epoch |-> 1,
          sender |-> B,
          receiver |-> A,
          contents |->
              { [ term |-> 1,
                  index |-> 1,
                  part |-> 0,
                  value |-> "NoValue",
                  kind |-> "noop",
                  prevSize |-> 0 ] },
          target |->
              [ term |-> 1,
                index |-> 1,
                part |-> 0,
                value |-> "NoValue",
                kind |-> "noop",
                prevSize |-> 0 ] ] } @@
  B :> {} @@
  C :> {} )
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

AppliedHistoryDiagnosticNext == pc = 21 /\ ApplyEntry(A, BoundaryBase) /\ Observe /\ GhostNext /\ pc' = 22
AppliedHistoryDiagnosticSpec == AppliedHistoryDiagnosticInit /\ [][AppliedHistoryDiagnosticNext]_OfferDiagnosticVars
LegacyHistoryCandidate == Safety /\ PreHistoryOriginInvariant
HistoryOriginStrengtheningExcludesPredecessor == pc = 21 => ~ProofInvariant
=============================================================================
