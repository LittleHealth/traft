---------------------- MODULE TRaftPointCoreAliases07 ----------------------
EXTENDS TRaftPointCoreAliases06

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM PointCoreAliasCopyProposalEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : PointLift!CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY SMT, PointCoreAliasResult
   DEF CopyProposalEntry, PointLift!CopyProposalEntry

THEOREM PointCoreAliasRetainProposal ==
    \A aliasArg1, aliasArg2 : PointLift!RetainProposal(aliasArg1, aliasArg2) = RetainProposal(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasResult
   DEF RetainProposal, PointLift!RetainProposal

THEOREM PointCoreAliasAckProposal ==
    \A aliasArg1, aliasArg2 : PointLift!AckProposal(aliasArg1, aliasArg2) = AckProposal(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasResult, PointCoreAliasAck
   DEF AckProposal, PointLift!AckProposal

THEOREM PointCoreAliasDeliverAck ==
    \A aliasArg1, aliasArg2 : PointLift!DeliverAck(aliasArg1, aliasArg2) = DeliverAck(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverAck, PointLift!DeliverAck

THEOREM PointCoreAliasConfirmProposal ==
    \A aliasArg1 : PointLift!ConfirmProposal(aliasArg1) = ConfirmProposal(aliasArg1)
BY ONLY SMT, PointCoreAliasNoProposal, PointCoreAliasQuorum, PointCoreAliasProposalAckers, PointCoreAliasPublish
   DEF ConfirmProposal, PointLift!ConfirmProposal

THEOREM PointCoreAliasLearnConfirmation ==
    \A aliasArg1, aliasArg2 : PointLift!LearnConfirmation(aliasArg1, aliasArg2) = LearnConfirmation(aliasArg1, aliasArg2)
BY ONLY SMT, PointCoreAliasResult, PointCoreAliasPublish
   DEF LearnConfirmation, PointLift!LearnConfirmation
=============================================================================
