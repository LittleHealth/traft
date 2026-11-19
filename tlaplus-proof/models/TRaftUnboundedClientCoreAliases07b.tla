---------------------- MODULE TRaftUnboundedClientCoreAliases07b ----------------------
EXTENDS TRaftUnboundedClientCoreAliases07

\* Continuation of the same checked definition identities; no new assumption.

THEOREM UnboundedClientCoreAliasCommitEntry ==
    \A aliasArg1, aliasArg2 : UnboundedClient!CommitEntry(aliasArg1, aliasArg2) = CommitEntry(aliasArg1, aliasArg2)
<1>1. ASSUME NEW c, NEW e
      PROVE UnboundedClient!CommitEntry(c, e) = CommitEntry(c, e)
    <2>1. UnboundedClient!Prefix(formal[c], e.part - 1) = Prefix(formal[c], e.part - 1)
        BY ONLY UnboundedClientCoreAliasPrefix
    <2>2. UnboundedClient!Ackers(c, term[c], e) = Ackers(c, term[c], e)
        BY ONLY UnboundedClientCoreAliasAckers
    <2>3. UnboundedClient!Quorum(Ackers(c, term[c], e)) = Quorum(Ackers(c, term[c], e))
        BY ONLY UnboundedClientCoreAliasQuorum
    <2> QED BY ONLY ZenonT(10), <2>1, <2>2, <2>3, UnboundedClientConstantSelections
       DEF CommitEntry, UnboundedClient!CommitEntry
<1> QED BY ONLY <1>1

THEOREM UnboundedClientCoreAliasAdvertiseCommit ==
    \A aliasArg1, aliasArg2 : UnboundedClient!AdvertiseCommit(aliasArg1, aliasArg2) = AdvertiseCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF AdvertiseCommit, UnboundedClient!AdvertiseCommit

THEOREM UnboundedClientCoreAliasLearnCommit ==
    \A aliasArg1, aliasArg2 : UnboundedClient!LearnCommit(aliasArg1, aliasArg2) = LearnCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF LearnCommit, UnboundedClient!LearnCommit

THEOREM UnboundedClientCoreAliasActivate ==
    \A aliasArg1 : UnboundedClient!Activate(aliasArg1) = Activate(aliasArg1)
BY ONLY SMT, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasResult
   DEF Activate, UnboundedClient!Activate
=============================================================================
