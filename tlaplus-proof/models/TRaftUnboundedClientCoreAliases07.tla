-------------------- MODULE TRaftUnboundedClientCoreAliases07 --------------------
EXTENDS TRaftUnboundedClientCoreAliases06

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedClientCoreAliasCopyProposalEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : UnboundedClient!CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY SMT, UnboundedClientCoreAliasResult
   DEF CopyProposalEntry, UnboundedClient!CopyProposalEntry

THEOREM UnboundedClientCoreAliasRetainProposal ==
    \A aliasArg1, aliasArg2 : UnboundedClient!RetainProposal(aliasArg1, aliasArg2) = RetainProposal(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasResult
   DEF RetainProposal, UnboundedClient!RetainProposal

THEOREM UnboundedClientCoreAliasAckProposal ==
    \A aliasArg1, aliasArg2 : UnboundedClient!AckProposal(aliasArg1, aliasArg2) = AckProposal(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasResult, UnboundedClientCoreAliasAck
   DEF AckProposal, UnboundedClient!AckProposal

THEOREM UnboundedClientCoreAliasDeliverAck ==
    \A aliasArg1, aliasArg2 : UnboundedClient!DeliverAck(aliasArg1, aliasArg2) = DeliverAck(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverAck, UnboundedClient!DeliverAck

THEOREM UnboundedClientCoreAliasConfirmProposal ==
    \A aliasArg1 : UnboundedClient!ConfirmProposal(aliasArg1) = ConfirmProposal(aliasArg1)
BY ONLY SMT, UnboundedClientConstantSelections, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasQuorum, UnboundedClientCoreAliasProposalAckers, UnboundedClientCoreAliasPublish
   DEF ConfirmProposal, UnboundedClient!ConfirmProposal

THEOREM UnboundedClientCoreAliasLearnConfirmation ==
    \A aliasArg1, aliasArg2 : UnboundedClient!LearnConfirmation(aliasArg1, aliasArg2) = LearnConfirmation(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedClientCoreAliasResult, UnboundedClientCoreAliasPublish
   DEF LearnConfirmation, UnboundedClient!LearnConfirmation
=============================================================================
