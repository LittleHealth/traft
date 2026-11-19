---------------------- MODULE TRaftLiftedCoreAliases07 ----------------------
EXTENDS TRaftLiftedCoreAliases06

\* Small, acyclic definition-identity obligations. Every preceding module
\* must pass its own complete proof check; imports alone are not evidence.

THEOREM LiftedCoreAliasCopyProposalEntry ==
    \A aliasArg1, aliasArg2, aliasArg3, aliasArg4 : LiftedSafety!CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4) = CopyProposalEntry(aliasArg1, aliasArg2, aliasArg3, aliasArg4)
BY ONLY SMT, LiftedCoreAliasResult
   DEF CopyProposalEntry, LiftedSafety!CopyProposalEntry

THEOREM LiftedCoreAliasRetainProposal ==
    \A aliasArg1, aliasArg2 : LiftedSafety!RetainProposal(aliasArg1, aliasArg2) = RetainProposal(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasResult
   DEF RetainProposal, LiftedSafety!RetainProposal

THEOREM LiftedCoreAliasAckProposal ==
    \A aliasArg1, aliasArg2 : LiftedSafety!AckProposal(aliasArg1, aliasArg2) = AckProposal(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasResult, LiftedCoreAliasAck
   DEF AckProposal, LiftedSafety!AckProposal

THEOREM LiftedCoreAliasDeliverAck ==
    \A aliasArg1, aliasArg2 : LiftedSafety!DeliverAck(aliasArg1, aliasArg2) = DeliverAck(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF DeliverAck, LiftedSafety!DeliverAck

THEOREM LiftedCoreAliasConfirmProposal ==
    \A aliasArg1 : LiftedSafety!ConfirmProposal(aliasArg1) = ConfirmProposal(aliasArg1)
BY ONLY SMT, LiftedCoreAliasNoProposal, LiftedCoreAliasQuorum, LiftedCoreAliasProposalAckers, LiftedCoreAliasPublish
   DEF ConfirmProposal, LiftedSafety!ConfirmProposal

THEOREM LiftedCoreAliasLearnConfirmation ==
    \A aliasArg1, aliasArg2 : LiftedSafety!LearnConfirmation(aliasArg1, aliasArg2) = LearnConfirmation(aliasArg1, aliasArg2)
BY ONLY SMT, LiftedCoreAliasResult, LiftedCoreAliasPublish
   DEF LearnConfirmation, LiftedSafety!LearnConfirmation
=============================================================================
