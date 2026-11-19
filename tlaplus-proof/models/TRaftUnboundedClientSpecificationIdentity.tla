-------------------- MODULE TRaftUnboundedClientSpecificationIdentity --------------------
EXTENDS TRaftUnboundedClientObserverIdentity


THEOREM UnboundedClientSpecificationIdentity == ClientSpec <=> UnboundedClient!ClientSpec
<1>1. (UnboundedClient!clientVars = clientVars)'
    BY ONLY PTL, UnboundedClientVariablesIdentity
<1>2. [UnboundedClient!ClientAction /\ UnboundedClient!Observe
          /\ UnboundedClient!ObserveLinearization]_UnboundedClient!clientVars
      <=> [ClientAction /\ Observe /\ ObserveLinearization]_clientVars
    BY ONLY SMT, UnboundedClientAliasClientAction, UnboundedClientCoreAliasObserve,
       UnboundedClientObserverIdentity, UnboundedClientVariablesIdentity, <1>1
<1> QED BY ONLY PTL, UnboundedClientInitialIdentity, <1>2
   DEF ClientSpec, UnboundedClient!ClientSpec,
       ClientSpecification, UnboundedClient!ClientSpecification
=============================================================================
