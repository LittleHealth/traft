--------------------------- MODULE TRaftFiniteState --------------------------
EXTENDS TRaftDurabilityState

\* Per-prefix finiteness; the domains of epochs and identifiers stay unbounded.
\* partitionHistory is deliberately excluded: its observer ranges over Terms.
FiniteChannelVars == <<voteRequests, voteMessages, recoveryRequests,
    reportMessages, offers, proposals, ackMessages, confirmations, commitMessages>>
FiniteNodeVars == <<formal, stored, retained, proposals>>
FiniteSnapshotVars == <<reportMessages, voteRequests, proposals>>
FiniteChannels == \A S \in {voteRequests, voteMessages, recoveryRequests,
      reportMessages, offers, proposals, ackMessages, confirmations, commitMessages} : IsFiniteSet(S)
FiniteNodeData ==
    /\ StorageShape /\ formal = [r \in Replicas |-> formal[r]]
    /\ retained \in [Replicas -> SUBSET proposals]
    /\ \A r \in Replicas : IsFiniteSet(formal[r]) /\ IsFiniteSet(stored[r])
                           /\ IsFiniteSet(retained[r])
FiniteProposals == \A p \in proposals : IsFiniteSet(Result(p))
FiniteSnapshots ==
    /\ \A m \in reportMessages : IsFiniteSet(m.entries)
          /\ IsFiniteSet(m.pending) /\ m.pending \subseteq proposals
    /\ \A req \in voteRequests : IsFiniteSet(req.entries)
FiniteLogInvariant == FiniteChannels /\ FiniteNodeData /\ FiniteProposals /\ FiniteSnapshots
FiniteLogVars == <<stored, formal, retained, voteRequests, voteMessages,
    recoveryRequests, reportMessages, offers, proposals, ackMessages, confirmations, commitMessages>>
=============================================================================
