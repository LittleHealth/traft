--------------------- MODULE TRaftBoundedMappingAliases ----------------------
EXTENDS TRaftBoundedParameterProof

THEOREM PhysicalActionsIgnorePartitionHistoryMapping ==
    Infinite!ProtocolNext <=> MappedCore!ProtocolNext
BY
   DEF Infinite!Ack, MappedCore!Ack, Infinite!AckEntry, MappedCore!AckEntry, Infinite!AckProposal,
       MappedCore!AckProposal, Infinite!Ackers, MappedCore!Ackers, Infinite!Activate,
       MappedCore!Activate, Infinite!AdministrativeNext, MappedCore!AdministrativeNext,
       Infinite!AdoptTerm, MappedCore!AdoptTerm, Infinite!AdvertiseCommit,
       MappedCore!AdvertiseCommit, Infinite!Aligned, MappedCore!Aligned, Infinite!ApplyEntry,
       MappedCore!ApplyEntry, Infinite!AtLeast, MappedCore!AtLeast, Infinite!BuildRecovery,
       MappedCore!BuildRecovery, Infinite!CanReceive, MappedCore!CanReceive, Infinite!CommitEntry,
       MappedCore!CommitEntry, Infinite!ConfirmProposal, MappedCore!ConfirmProposal,
       Infinite!CopyProposalEntry, MappedCore!CopyProposalEntry, Infinite!Count, MappedCore!Count,
       Infinite!Crash, MappedCore!Crash, Infinite!CreateEntry, MappedCore!CreateEntry,
       Infinite!CreateSuccessor, MappedCore!CreateSuccessor, Infinite!Cur, MappedCore!Cur,
       Infinite!DeliverAck, MappedCore!DeliverAck, Infinite!DeliverReport, MappedCore!DeliverReport,
       Infinite!DeliverVote, MappedCore!DeliverVote, Infinite!EmptyReports, MappedCore!EmptyReports,
       Infinite!Entry, MappedCore!Entry, Infinite!GrantVote, MappedCore!GrantVote, Infinite!Indices,
       MappedCore!Indices, Infinite!LastIndex, MappedCore!LastIndex, Infinite!LastTerm,
       MappedCore!LastTerm, Infinite!Later, MappedCore!Later, Infinite!Latest, MappedCore!Latest,
       Infinite!LearnCommit, MappedCore!LearnCommit, Infinite!LearnConfirmation,
       MappedCore!LearnConfirmation, Infinite!MakeReport, MappedCore!MakeReport, Infinite!MaxOr,
       MappedCore!MaxOr, Infinite!MessageAckers, MappedCore!MessageAckers, Infinite!NoNode,
       MappedCore!NoNode, Infinite!NoProposal, MappedCore!NoProposal, Infinite!NoReport,
       MappedCore!NoReport, Infinite!NormalMessage, MappedCore!NormalMessage, Infinite!Origin,
       MappedCore!Origin, Infinite!Part, MappedCore!Part, Infinite!Partitions,
       MappedCore!Partitions, Infinite!Prefix, MappedCore!Prefix, Infinite!Proposal,
       MappedCore!Proposal, Infinite!ProposalAckers, MappedCore!ProposalAckers,
       Infinite!ProtocolNext, MappedCore!ProtocolNext, Infinite!Publish, MappedCore!Publish,
       Infinite!Quorum, MappedCore!Quorum, Infinite!Rank, MappedCore!Rank, Infinite!ReceiveEntry,
       MappedCore!ReceiveEntry, Infinite!Recovered, MappedCore!Recovered, Infinite!ReportedEntries,
       MappedCore!ReportedEntries, Infinite!ReportedProposals, MappedCore!ReportedProposals,
       Infinite!Reporters, MappedCore!Reporters, Infinite!Restart, MappedCore!Restart,
       Infinite!Result, MappedCore!Result, Infinite!RetainProposal, MappedCore!RetainProposal,
       Infinite!SendEntry, MappedCore!SendEntry, Infinite!StartElection, MappedCore!StartElection,
       Infinite!Terms, MappedCore!Terms, Infinite!WinElection, MappedCore!WinElection,
       Infinite!IsFiniteSet, MappedCore!IsFiniteSet, Infinite!Cardinality, MappedCore!Cardinality

THEOREM InitialPartitionHistoryMapping == Init => MappedCore!Init
BY EpochClosureOfEmpty
   DEF EmptyReports, MappedCore!EmptyReports, Init, MappedCore!Init, NoNode, MappedCore!NoNode,
       NoProposal, MappedCore!NoProposal, NoReport, MappedCore!NoReport, IsFiniteSet,
       MappedCore!IsFiniteSet, Cardinality, MappedCore!Cardinality

THEOREM MappedObserverLogOperators ==
    /\ \A L : MappedCore!Cur(L) = Cur(L)
    /\ \A L, p : MappedCore!Part(L, p) = Part(L, p)
    /\ \A L, p : MappedCore!Prefix(L, p) = Prefix(L, p)
BY ONLY ZenonT(10) DEF MappedCore!Cur, Cur, MappedCore!MaxOr, MaxOr,
    MappedCore!Part, Part, MappedCore!Prefix, Prefix

THEOREM MappedIndependentEvidence ==
    \A M : MappedCore!Evidence(M) = Infinite!Evidence(M)
<1>0. SUFFICES ASSUME NEW M
              PROVE MappedCore!Evidence(M) = Infinite!Evidence(M)
    OBVIOUS
<1>1. \A S : MappedCore!IsFiniteSet(S) = Infinite!IsFiniteSet(S)
    BY ONLY ZenonT(10) DEF MappedCore!IsFiniteSet, Infinite!IsFiniteSet
<1>2. \A S : MappedCore!Cardinality(S) = Infinite!Cardinality(S)
    BY ONLY ZenonT(10), <1>1 DEF MappedCore!Cardinality, Infinite!Cardinality
<1>3. \A S : MappedCore!Quorum(S) = Infinite!Quorum(S)
    BY ONLY <1>2 DEF MappedCore!Quorum, Infinite!Quorum
<1>4. \A c, t, e :
          MappedCore!MessageAckers(M, c, t, e) = Infinite!MessageAckers(M, c, t, e)
    BY ONLY DEF MappedCore!MessageAckers, Infinite!MessageAckers
<1>5. MappedCore!Terms = Infinite!Terms
    BY ONLY DEF MappedCore!Terms, Infinite!Terms
<1>6. \A c, t, e :
          MappedCore!Quorum(MappedCore!MessageAckers(M, c, t, e))
          = Infinite!Quorum(Infinite!MessageAckers(M, c, t, e))
    BY ONLY SMT, <1>3, <1>4
<1>7. \A t :
          {x \in (UNION {a.contents : a \in M}) :
             \E c \in Replicas : MappedCore!Quorum(MappedCore!MessageAckers(M, c, t, x))}
          = {x \in (UNION {a.contents : a \in M}) :
             \E c \in Replicas : Infinite!Quorum(Infinite!MessageAckers(M, c, t, x))}
    BY ONLY SMT, <1>6
<1> QED BY ONLY IsaM("auto"), <1>5, <1>7
    DEF MappedCore!Evidence, Infinite!Evidence

THEOREM MappedObservationIdentity == ExpandedObservation <=> MappedCore!Observe
<1>1. PresentWinners' = {[node |-> r, epoch |-> term'[r]] :
          r \in {x \in Replicas : role'[x] = "LeaderCandidate"}}
    BY ONLY SMT DEF PresentWinners
<1>2. PresentViews' = {[node |-> r, epoch |-> term'[r], entries |-> formal'[r]] :
          r \in {x \in Replicas : role'[x] = "Leader"}}
    BY ONLY SMT DEF PresentViews
<1>3. PresentContexts' =
          (UNION { {[entry |-> e, prefix |-> MappedCore!Prefix(formal'[r], e.part - 1)] :
             e \in {x \in formal'[r] : x.term = term'[r]}} :
             r \in {n \in Replicas : role'[n] = "Leader"}}) \cup
          {[entry |-> p.first, prefix |-> p.prefix] : p \in proposals'}
    BY ONLY SMT DEF PresentContexts, Prefix, MappedCore!Prefix
<1>4. UnboundedClosed' = (UNION {
          {[epoch |-> term'[r], part |-> q, entries |-> MappedCore!Part(formal'[r], q)] :
             q \in {j \in MappedCore!Partitions :
                  j < MappedCore!Cur(formal'[r]) /\ MappedCore!Part(formal'[r], j) # {}}} :
          r \in Replicas})
    BY ONLY IsaM("auto"), MappedObserverLogOperators, MappedIdentifierDomains
        DEF UnboundedClosed
<1>5. PresentAppliedPartitions' = (UNION {
          {[node |-> r, part |-> q, entries |-> MappedCore!Part(formal'[r], q)] :
             q \in {j \in 0..(MappedCore!Cur(formal'[r]) - 1) :
                  MappedCore!Part(formal'[r], j) # {}
                  /\ MappedCore!Part(formal'[r], j) \subseteq applied'[r]}} :
          r \in Replicas})
    BY ONLY SMT, MappedObserverLogOperators DEF PresentAppliedPartitions
<1>6. EpochClosure(partitionHistory)' = EpochClosure(partitionHistory')
    BY ONLY SMT DEF EpochClosure
<1> QED BY ONLY IsaM("auto"), <1>1, <1>2, <1>3, <1>4, <1>5, <1>6,
    MappedObserverLogOperators, MappedIndependentEvidence, MappedIdentifierDomains
    DEF MappedCore!Observe, ExpandedObservation, ObservationBooleans, CertifiedClosed

THEOREM UnchangedStateHasUnchangedMappedState ==
    UNCHANGED vars => UNCHANGED MappedCore!vars
BY DEF vars, protocolVars, observerVars,
       MappedCore!vars, MappedCore!protocolVars, MappedCore!observerVars
=============================================================================
