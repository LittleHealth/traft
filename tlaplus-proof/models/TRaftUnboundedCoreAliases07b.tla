---------------------- MODULE TRaftUnboundedCoreAliases07b ----------------------
EXTENDS TRaftUnboundedCoreAliases07

\* Continuation of the same checked definition identities; no new assumption.

THEOREM UnboundedCoreAliasCommitEntry ==
    \A aliasArg1, aliasArg2 : UnboundedCore!CommitEntry(aliasArg1, aliasArg2) = CommitEntry(aliasArg1, aliasArg2)
<1>1. ASSUME NEW c, NEW e
      PROVE UnboundedCore!CommitEntry(c, e) = CommitEntry(c, e)
    <2>1. UnboundedCore!Prefix(formal[c], e.part - 1) = Prefix(formal[c], e.part - 1)
        BY ONLY UnboundedCoreAliasPrefix
    <2>2. UnboundedCore!Ackers(c, term[c], e) = Ackers(c, term[c], e)
        BY ONLY UnboundedCoreAliasAckers
    <2>3. UnboundedCore!Quorum(Ackers(c, term[c], e)) = Quorum(Ackers(c, term[c], e))
        BY ONLY UnboundedCoreAliasQuorum
    <2> QED BY ONLY ZenonT(10), <2>1, <2>2, <2>3, UnboundedConstantSelections
       DEF CommitEntry, UnboundedCore!CommitEntry
<1> QED BY ONLY <1>1

THEOREM UnboundedCoreAliasAdvertiseCommit ==
    \A aliasArg1, aliasArg2 : UnboundedCore!AdvertiseCommit(aliasArg1, aliasArg2) = AdvertiseCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF AdvertiseCommit, UnboundedCore!AdvertiseCommit

THEOREM UnboundedCoreAliasLearnCommit ==
    \A aliasArg1, aliasArg2 : UnboundedCore!LearnCommit(aliasArg1, aliasArg2) = LearnCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF LearnCommit, UnboundedCore!LearnCommit

THEOREM UnboundedCoreAliasActivate ==
    \A aliasArg1 : UnboundedCore!Activate(aliasArg1) = Activate(aliasArg1)
BY ONLY SMT, UnboundedCoreAliasNoProposal, UnboundedCoreAliasResult
   DEF Activate, UnboundedCore!Activate
=============================================================================
