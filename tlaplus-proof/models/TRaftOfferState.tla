--------------------------- MODULE TRaftOfferState ---------------------------
EXTENDS TRaftCore

\* An observation of the real SendEntry action, never a receive-side guard.
OfferProvenance == \A o \in offers :
    \E v \in leaderViews :
        /\ v.node = o.owner /\ v.epoch = o.epoch
        /\ o.entry \in v.entries /\ o.entry.term = o.epoch
OfferVars == <<offers, leaderViews>>
=============================================================================
