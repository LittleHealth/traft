-------------------- MODULE TRaftUnboundedCoreAliases07 --------------------
EXTENDS TRaftUnboundedCoreAliases06

\* Same core definitions with the explicit unbounded constant selectors.
\* All identities and their imported dependencies require separate checks.

THEOREM UnboundedCoreAliasCopyProposalEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : UnboundedCore!CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY SMT, UnboundedCoreAliasResult
   DEF CopyProposalEntry, UnboundedCore!CopyProposalEntry

THEOREM UnboundedCoreAliasRetainProposal ==
    \A aliasArg1, aliasArg2 : UnboundedCore!RetainProposal(aliasArg1, aliasArg2) = RetainProposal(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasResult
   DEF RetainProposal, UnboundedCore!RetainProposal

THEOREM UnboundedCoreAliasAckProposal ==
    \A aliasArg1, aliasArg2 : UnboundedCore!AckProposal(aliasArg1, aliasArg2) = AckProposal(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasResult, UnboundedCoreAliasAck
   DEF AckProposal, UnboundedCore!AckProposal

THEOREM UnboundedCoreAliasDeliverAck ==
    \A aliasArg1, aliasArg2 : UnboundedCore!DeliverAck(aliasArg1, aliasArg2) = DeliverAck(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverAck, UnboundedCore!DeliverAck

THEOREM UnboundedCoreAliasConfirmProposal ==
    \A aliasArg1 : UnboundedCore!ConfirmProposal(aliasArg1) = ConfirmProposal(aliasArg1)
BY ONLY SMT, UnboundedConstantSelections, UnboundedCoreAliasNoProposal, UnboundedCoreAliasQuorum, UnboundedCoreAliasProposalAckers, UnboundedCoreAliasPublish
   DEF ConfirmProposal, UnboundedCore!ConfirmProposal

THEOREM UnboundedCoreAliasLearnConfirmation ==
    \A aliasArg1, aliasArg2 : UnboundedCore!LearnConfirmation(aliasArg1, aliasArg2) = LearnConfirmation(aliasArg1, aliasArg2)
BY ONLY SMT, UnboundedCoreAliasResult, UnboundedCoreAliasPublish
   DEF LearnConfirmation, UnboundedCore!LearnConfirmation
=============================================================================
