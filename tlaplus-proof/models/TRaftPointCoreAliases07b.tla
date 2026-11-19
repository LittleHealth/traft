---------------------- MODULE TRaftPointCoreAliases07b ----------------------
EXTENDS TRaftPointCoreAliases07

\* Continuation of the same checked definition identities; no new assumption.

THEOREM PointCoreAliasCommitEntry ==
    \A aliasArg1, aliasArg2 : PointLift!CommitEntry(aliasArg1, aliasArg2) = CommitEntry(aliasArg1, aliasArg2)
<1>1. ASSUME NEW c, NEW e
      PROVE PointLift!CommitEntry(c, e) = CommitEntry(c, e)
    <2>1. PointLift!Prefix(formal[c], e.part - 1) = Prefix(formal[c], e.part - 1)
        BY ONLY PointCoreAliasPrefix
    <2>2. PointLift!Ackers(c, term[c], e) = Ackers(c, term[c], e)
        BY ONLY PointCoreAliasAckers
    <2>3. PointLift!Quorum(Ackers(c, term[c], e)) = Quorum(Ackers(c, term[c], e))
        BY ONLY PointCoreAliasQuorum
    <2> QED BY ONLY ZenonT(10), <2>1, <2>2, <2>3
       DEF CommitEntry, PointLift!CommitEntry
<1> QED BY ONLY <1>1

THEOREM PointCoreAliasAdvertiseCommit ==
    \A aliasArg1, aliasArg2 : PointLift!AdvertiseCommit(aliasArg1, aliasArg2) = AdvertiseCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF AdvertiseCommit, PointLift!AdvertiseCommit

THEOREM PointCoreAliasLearnCommit ==
    \A aliasArg1, aliasArg2 : PointLift!LearnCommit(aliasArg1, aliasArg2) = LearnCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF LearnCommit, PointLift!LearnCommit

THEOREM PointCoreAliasActivate ==
    \A aliasArg1 : PointLift!Activate(aliasArg1) = Activate(aliasArg1)
BY ONLY SMT, PointCoreAliasNoProposal, PointCoreAliasResult
   DEF Activate, PointLift!Activate
=============================================================================
