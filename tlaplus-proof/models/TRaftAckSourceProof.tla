------------------------- MODULE TRaftAckSourceProof -------------------------
EXTENDS TRaftAckSourceState, TRaftAckSourceFrames, TRaftOfferProof,
        TRaftHistoryRefinementProof, TRaftRetainedFrames, TRaftDurabilityProof, TRaftCommitFrames

THEOREM AckSourceSurvivesGrowth ==
    ASSUME NEW a, NEW P, NEW Q, NEW O, NEW U,
           AckHasSource(a, P, O), P \subseteq Q, O \subseteq U
    PROVE AckHasSource(a, Q, U)
BY SMT DEF AckHasSource

THEOREM OffersNeverShrink == ProtocolNext => offers \subseteq offers'
<1>1. \A c, e : SendEntry(c, e) => offers \subseteq offers'
    BY SMT DEF SendEntry
<1> QED BY SMT, <1>1, OnlySendEntryCreatesOffer

THEOREM AckSourcesInductiveStep ==
    ASSUME AckSourceInvariant, \A r \in Replicas : retained[r] \subseteq proposals,
           ProtocolNext
    PROVE AckSourceInvariant'
<1>1. proposals \subseteq proposals' /\ offers \subseteq offers'
    BY ProposalsNeverShrink, OffersNeverShrink
<1>2. \A a \in ackMessages : AckHasSource(a, proposals', offers')
    BY SMT, AckSourceSurvivesGrowth, <1>1 DEF AckSourceInvariant
<1>3. (\E r \in Replicas : \E o : AckEntry(r, o))
          \/ (\E r \in Replicas : \E p : AckProposal(r, p)) \/ UNCHANGED ackMessages
    BY OnlyAckActionsChangeMessages
<1>4. ASSUME NEW r \in Replicas, NEW o, AckEntry(r, o)
      PROVE AckSourceInvariant'
    <2>1. o \in offers' /\ ackMessages' = ackMessages \cup {Ack(r, o.owner, o.epoch, o.entry, {o.entry})}
        BY SMT, <1>1, <1>4 DEF AckEntry
    <2> QED BY SMT, <1>2, <2>1 DEF AckSourceInvariant, AckHasSource, Ack
<1>5. ASSUME NEW r \in Replicas, NEW p, AckProposal(r, p)
      PROVE AckSourceInvariant'
    <2>1. p \in proposals' /\ ackMessages' = ackMessages \cup {Ack(r, p.owner, p.epoch, p.first, Result(p))}
        BY SMT, <1>1, <1>5 DEF AckProposal
    <2> QED BY SMT, <1>2, <2>1 DEF AckSourceInvariant, AckHasSource, Ack
<1> QED BY SMT, <1>2, <1>3, <1>4, <1>5 DEF AckSourceInvariant

THEOREM AckSourcesInitially == Init => AckSourceInvariant
BY SMT DEF Init, AckSourceInvariant

THEOREM AckSourcesStuttering ==
    ASSUME AckSourceInvariant, UNCHANGED vars
    PROVE AckSourceInvariant'
BY SMT DEF AckSourceInvariant, AckHasSource, vars, protocolVars, observerVars

THEOREM RetainedSourcesInductiveStep ==
    ASSUME RetainedShape, RetainedProposalsActual, ProtocolNext
    PROVE RetainedProposalsActual'
<1>1. proposals \subseteq proposals'
    BY ProposalsNeverShrink
<1>2. (\E r \in Replicas : \E p : RetainProposal(r, p)) \/ UNCHANGED retained
    BY OnlyRetainChangesRetained
<1>3. ASSUME NEW r \in Replicas, NEW p, RetainProposal(r, p)
      PROVE RetainedProposalsActual'
    BY SMT, <1>1, <1>3 DEF RetainProposal, RetainedShape, RetainedProposalsActual
<1> QED BY SMT, <1>1, <1>2, <1>3 DEF RetainedProposalsActual

THEOREM ConfirmationSourcesInductiveStep ==
    ASSUME ConfirmationSources, RetainedProposalsActual, ProtocolNext
    PROVE ConfirmationSources'
<1>1. proposals \subseteq proposals'
    BY ProposalsNeverShrink
<1>2. KnowledgeChangingNext \/ UNCHANGED <<knownCommitted, commitMessages, confirmations>>
    BY ProtocolKnowledgeProjection
<1>3. \A c \in Replicas : ConfirmProposal(c) => ConfirmationSources'
    BY SMT, <1>1 DEF ConfirmProposal, ConfirmationSources, RetainedProposalsActual
<1> QED BY SMT, <1>1, <1>2, <1>3 DEF KnowledgeChangingNext,
    CommitEntry, AdvertiseCommit, LearnCommit, ConfirmationSources

THEOREM MessageSourcesInductiveStep ==
    ASSUME MessageSourceInvariant, RetainedShape, ProtocolNext
    PROVE MessageSourceInvariant'
BY AckSourcesInductiveStep, RetainedSourcesInductiveStep, ConfirmationSourcesInductiveStep
   DEF MessageSourceInvariant, RetainedProposalsActual

THEOREM MessageSourcesInitially == Init => MessageSourceInvariant
BY SMT DEF Init, MessageSourceInvariant, AckSourceInvariant, RetainedProposalsActual, ConfirmationSources

THEOREM MessageSourcesStuttering ==
    ASSUME MessageSourceInvariant, UNCHANGED vars
    PROVE MessageSourceInvariant'
BY SMT DEF MessageSourceInvariant, AckSourceInvariant, AckHasSource,
    RetainedProposalsActual, ConfirmationSources, vars, protocolVars, observerVars

THEOREM ProtocolMessageSources == Spec => []MessageSourceInvariant
<1>1. Spec => []RetainedShape
    BY PTL, ProtocolAckDurability DEF DurabilityInvariant, DurableData
<1>2. Init => MessageSourceInvariant
    BY MessageSourcesInitially
<1>3. MessageSourceInvariant /\ RetainedShape /\ [Next]_vars => MessageSourceInvariant'
    BY MessageSourcesInductiveStep, MessageSourcesStuttering DEF Next
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec

THEOREM ProtocolAckSources == Spec => []AckSourceInvariant /\ []ConfirmationSources
BY PTL, ProtocolMessageSources DEF MessageSourceInvariant
=============================================================================
