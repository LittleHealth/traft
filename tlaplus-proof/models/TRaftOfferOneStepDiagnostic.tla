--------------------- MODULE TRaftOfferOneStepDiagnostic ---------------------
EXTENDS TRaftOfferDiagnostic

\* The predecessor of the failing ReceiveEntry step, extracted from TLC.
\* Synthetic offer channel: this is an induction countermodel, not a
\* protocol execution from Init. Source log SHA256:
\* 90f36c68661e900b8204c56ac92e6fdfb056915e01872c331f8f0c2a67569eab

OfferSnapshotInit ==
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
/\ leaderViews = { [ epoch |-> 1,
    entries |->
        { [ term |-> 1,
            index |-> 1,
            part |-> 0,
            value |-> "NoValue",
            kind |-> "noop",
            prevSize |-> 0 ] },
    node |-> A ] }
/\ canonical = ( 0 :> {} @@
  1 :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  2 :> {} @@
  3 :> {} )
/\ voteInbox = ( A :>
      { [epoch |-> 1, sender |-> A, receiver |-> A],
        [epoch |-> 1, sender |-> B, receiver |-> A] } @@
  B :> {} @@
  C :> {} )
/\ formal = ( A :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  B :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  C :> {} )
/\ entryContexts = { [ entry |->
        [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ],
    prefix |-> {} ] }
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
/\ appliedPartitionHistory = {}
/\ stored = ( A :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  B :>
      { [ term |-> 1,
          index |-> 1,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "noop",
          prevSize |-> 0 ] } @@
  C :> {} )
/\ winners = {[epoch |-> 1, node |-> A]}
/\ phase = (A :> "serve" @@ B :> "idle" @@ C :> "idle")
/\ offers = { [ owner |-> A,
    epoch |-> 1,
    entry |->
        [ term |-> 1,
          index |-> 2,
          part |-> 0,
          value |-> "NoValue",
          kind |-> "data",
          prevSize |-> 0 ],
    committed |-> 0 ] }
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

OfferSnapshotNext == ReceiveEntry(B, BadOffer) /\ Observe /\ GhostNext /\ UNCHANGED pc
OfferSnapshotSpec == OfferSnapshotInit /\ [][OfferSnapshotNext]_OfferDiagnosticVars
=============================================================================
