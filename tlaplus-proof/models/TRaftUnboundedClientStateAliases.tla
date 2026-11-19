-------------------- MODULE TRaftUnboundedClientStateAliases --------------------
EXTENDS TRaftUnboundedClientAliases02


THEOREM UnboundedClientEmptyMachineIdentity == UnboundedClient!EmptyMachine = EmptyMachine
BY ONLY SMT, UnboundedClientAliasKeys
   DEF UnboundedClient!EmptyMachine, EmptyMachine

THEOREM UnboundedClientEmptyAnswersIdentity == UnboundedClient!EmptyAnswers = EmptyAnswers
BY ONLY SMT, UnboundedClientAliasRequestIds
   DEF UnboundedClient!EmptyAnswers, EmptyAnswers

THEOREM UnboundedClientInitialIdentity == UnboundedClient!ClientInit <=> ClientInit
BY ONLY SMT, UnboundedClientCoreAliasInit, UnboundedClientAliasEmptyCache,
   UnboundedClientEmptyMachineIdentity, UnboundedClientEmptyAnswersIdentity
   DEF UnboundedClient!ClientInit, ClientInit

THEOREM UnboundedClientVariablesIdentity == UnboundedClient!clientVars = clientVars
BY ONLY SMT, UnboundedClientCoreAliasvars, UnboundedClientAliaslocalClientVars
   DEF UnboundedClient!clientVars, clientVars, UnboundedClient!witnessVars, witnessVars
=============================================================================
