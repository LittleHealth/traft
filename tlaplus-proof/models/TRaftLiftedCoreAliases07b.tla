---------------------- MODULE TRaftLiftedCoreAliases07b ----------------------
EXTENDS TRaftLiftedCoreAliases07

\* Continuation of the same checked definition identities; no new assumption.

THEOREM LiftedCoreAliasCommitEntry ==
    \A aliasArg1, aliasArg2 : LiftedSafety!CommitEntry(aliasArg1, aliasArg2) = CommitEntry(aliasArg1, aliasArg2)
<1>1. ASSUME NEW c, NEW e
      PROVE LiftedSafety!CommitEntry(c, e) = CommitEntry(c, e)
    <2>1. LiftedSafety!Prefix(formal[c], e.part - 1) = Prefix(formal[c], e.part - 1)
        BY ONLY LiftedCoreAliasPrefix
    <2>2. LiftedSafety!Ackers(c, term[c], e) = Ackers(c, term[c], e)
        BY ONLY LiftedCoreAliasAckers
    <2>3. LiftedSafety!Quorum(Ackers(c, term[c], e)) = Quorum(Ackers(c, term[c], e))
        BY ONLY LiftedCoreAliasQuorum
    <2> QED BY ONLY ZenonT(10), <2>1, <2>2, <2>3
       DEF CommitEntry, LiftedSafety!CommitEntry
<1> QED BY ONLY <1>1

THEOREM LiftedCoreAliasAdvertiseCommit ==
    \A aliasArg1, aliasArg2 : LiftedSafety!AdvertiseCommit(aliasArg1, aliasArg2) = AdvertiseCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF AdvertiseCommit, LiftedSafety!AdvertiseCommit

THEOREM LiftedCoreAliasLearnCommit ==
    \A aliasArg1, aliasArg2 : LiftedSafety!LearnCommit(aliasArg1, aliasArg2) = LearnCommit(aliasArg1, aliasArg2)
BY ONLY SMT
   DEF LearnCommit, LiftedSafety!LearnCommit

THEOREM LiftedCoreAliasActivate ==
    \A aliasArg1 : LiftedSafety!Activate(aliasArg1) = Activate(aliasArg1)
BY ONLY SMT, LiftedCoreAliasNoProposal, LiftedCoreAliasResult
   DEF Activate, LiftedSafety!Activate
=============================================================================
