---------------------- MODULE TRaftUnboundedClientAliases02 ----------------------
EXTENDS TRaftUnboundedClientAliases01

\* Definition equalities only; no protocol guard or safety assumption.

THEOREM UnboundedClientAliasInvoke ==
    \A q : UnboundedClient!Invoke(q) = Invoke(q)
BY ONLY SMT, UnboundedClientAliasClientCommands, UnboundedClientAliasReturnedIds
   DEF Invoke, UnboundedClient!Invoke, protocolVars, UnboundedClient!protocolVars

THEOREM UnboundedClientAliasAdmit ==
    \A r, q : UnboundedClient!Admit(r, q) = Admit(r, q)
BY ONLY SMT, UnboundedClientAliasMustSeparate, UnboundedClientCoreAliasCreateSuccessor, UnboundedClientCoreAliasCreateEntry, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasCur
   DEF Admit, UnboundedClient!Admit, localClientVars, UnboundedClient!localClientVars

THEOREM UnboundedClientAliasClosePartition ==
    \A r : UnboundedClient!ClosePartition(r) = ClosePartition(r)
BY ONLY SMT, UnboundedClientCoreAliasCreateSuccessor
   DEF ClosePartition, UnboundedClient!ClosePartition, localClientVars, UnboundedClient!localClientVars

THEOREM UnboundedClientAliasApplyClient ==
    \A r, e : UnboundedClient!ApplyClient(r, e) = ApplyClient(r, e)
BY ONLY SMT, UnboundedClientCoreAliasApplyEntry, UnboundedClientAliasEffect, UnboundedClientAliasReply
   DEF ApplyClient, UnboundedClient!ApplyClient

THEOREM UnboundedClientAliasBackground ==
    UnboundedClient!Background = Background
BY ONLY SMT, UnboundedClientCoreAliasAdministrativeNext, UnboundedClientAliasEmptyCache, UnboundedClientConstantSelections
   DEF Background, UnboundedClient!Background

THEOREM UnboundedClientAliasSendReply ==
    \A r, q : UnboundedClient!SendReply(r, q) = SendReply(r, q)
BY ONLY SMT, UnboundedClientAliasReply, UnboundedClientConstantSelections
   DEF SendReply, UnboundedClient!SendReply, protocolVars, UnboundedClient!protocolVars

THEOREM UnboundedClientAliasReadWithoutBarrier ==
    \A r, q : UnboundedClient!ReadWithoutBarrier(r, q) = ReadWithoutBarrier(r, q)
BY ONLY SMT, UnboundedClientConstantSelections
   DEF ReadWithoutBarrier, UnboundedClient!ReadWithoutBarrier, protocolVars, UnboundedClient!protocolVars

THEOREM UnboundedClientAliasReceiveReply ==
    \A m : UnboundedClient!ReceiveReply(m) = ReceiveReply(m)
BY ONLY SMT, UnboundedClientAliasReturnedIds
   DEF ReceiveReply, UnboundedClient!ReceiveReply, protocolVars, UnboundedClient!protocolVars

THEOREM UnboundedClientAliasClientAction ==
    UnboundedClient!ClientAction = ClientAction
BY ONLY SMT, UnboundedClientAliasBackground, UnboundedClientAliasClientCommands, UnboundedClientAliasInvoke, UnboundedClientAliasAdmit, UnboundedClientAliasSendReply, UnboundedClientAliasReadWithoutBarrier, UnboundedClientAliasClosePartition, UnboundedClientAliasApplyClient, UnboundedClientAliasReceiveReply
   DEF ClientAction, UnboundedClient!ClientAction

=============================================================================
