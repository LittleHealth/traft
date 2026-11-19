---------------------- MODULE TRaftPointClientAliases02 ----------------------
EXTENDS TRaftPointClientAliases01

\* Definition equalities only; no protocol guard or safety assumption.

THEOREM PointClientAliasInvoke ==
    \A q : PointLift!Invoke(q) = Invoke(q)
BY ONLY SMT, PointClientAliasClientCommands, PointClientAliasReturnedIds
   DEF Invoke, PointLift!Invoke, protocolVars, PointLift!protocolVars

THEOREM PointClientAliasAdmit ==
    \A r, q : PointLift!Admit(r, q) = Admit(r, q)
BY ONLY SMT, PointClientAliasMustSeparate, PointCoreAliasCreateSuccessor, PointCoreAliasCreateEntry, PointCoreAliasCount, PointCoreAliasCur
   DEF Admit, PointLift!Admit, localClientVars, PointLift!localClientVars

THEOREM PointClientAliasClosePartition ==
    \A r : PointLift!ClosePartition(r) = ClosePartition(r)
BY ONLY SMT, PointCoreAliasCreateSuccessor
   DEF ClosePartition, PointLift!ClosePartition, localClientVars, PointLift!localClientVars

THEOREM PointClientAliasApplyClient ==
    \A r, e : PointLift!ApplyClient(r, e) = ApplyClient(r, e)
BY ONLY SMT, PointCoreAliasApplyEntry, PointClientAliasEffect, PointClientAliasReply
   DEF ApplyClient, PointLift!ApplyClient

THEOREM PointClientAliasBackground ==
    PointLift!Background = Background
BY ONLY SMT, PointCoreAliasAdministrativeNext, PointClientAliasEmptyCache
   DEF Background, PointLift!Background

THEOREM PointClientAliasSendReply ==
    \A r, q : PointLift!SendReply(r, q) = SendReply(r, q)
BY ONLY SMT, PointClientAliasReply
   DEF SendReply, PointLift!SendReply, protocolVars, PointLift!protocolVars

THEOREM PointClientAliasReadWithoutBarrier ==
    \A r, q : PointLift!ReadWithoutBarrier(r, q) = ReadWithoutBarrier(r, q)
BY ONLY SMT
   DEF ReadWithoutBarrier, PointLift!ReadWithoutBarrier, protocolVars, PointLift!protocolVars

THEOREM PointClientAliasReceiveReply ==
    \A m : PointLift!ReceiveReply(m) = ReceiveReply(m)
BY ONLY SMT, PointClientAliasReturnedIds
   DEF ReceiveReply, PointLift!ReceiveReply, protocolVars, PointLift!protocolVars

THEOREM PointClientAliasClientAction ==
    PointLift!ClientAction = ClientAction
BY ONLY SMT, PointClientAliasBackground, PointClientAliasClientCommands, PointClientAliasInvoke, PointClientAliasAdmit, PointClientAliasSendReply, PointClientAliasReadWithoutBarrier, PointClientAliasClosePartition, PointClientAliasApplyClient, PointClientAliasReceiveReply
   DEF ClientAction, PointLift!ClientAction

=============================================================================
