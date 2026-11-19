-------------------------- MODULE TRaftAckSourceState ------------------------
EXTENDS TRaftCore

AckHasSource(a, P, O) ==
    \/ \E p \in P : a = Ack(a.sender, p.owner, p.epoch, p.first, Result(p))
    \/ \E o \in O : a = Ack(a.sender, o.owner, o.epoch, o.entry, {o.entry})
AckSourceInvariant == \A a \in ackMessages : AckHasSource(a, proposals, offers)
RetainedProposalsActual == \A r \in Replicas : retained[r] \subseteq proposals
ConfirmationSources == confirmations \subseteq proposals
MessageSourceInvariant == AckSourceInvariant /\ RetainedProposalsActual /\ ConfirmationSources
=============================================================================
