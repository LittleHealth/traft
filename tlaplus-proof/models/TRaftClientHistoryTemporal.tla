--------------------- MODULE TRaftClientHistoryTemporal ----------------------
EXTENDS TRaftClientHistoryFacts, TRaftClientApplicationTemporal

THEOREM ClientHistorySourcesAlways ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []RequestHistoryState
<1>1. ClientSpecification(Extra) =>
          []RequestIdentityState /\ []ApplicationTypes /\ []ReplySources
    BY PTL, ClientRequestIdentityAlways, ClientApplicationFactsAlways,
       ClientRepliesHaveDurableSources
<1>2. ClientInit => RequestHistoryState
    BY RequestHistoryInitially
<1>3. RequestHistoryState /\ RequestIdentityState /\ ApplicationTypes /\ ReplySources
      /\ [ClientAction /\ Observe /\ Extra]_clientVars => RequestHistoryState'
    <2>1. RequestHistoryState /\ RequestIdentityState /\ ApplicationTypes /\ ReplySources
          /\ ClientAction => RequestHistoryState'
        BY RequestHistoryInductiveStep
    <2>2. RequestHistoryState /\ UNCHANGED clientVars => RequestHistoryState'
        BY DEF RequestHistoryState, HistoryCallSources, HistoryReturnSources, CalledIds,
               clientVars, localClientVars
    <2> QED BY <2>1, <2>2
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF ClientSpecification

THEOREM FiniteCallsHaveFiniteIdentities == IsFiniteSet(calls) => IsFiniteSet(CalledIds)
BY ONLY FS_Image, IsaM("blast") DEF CalledIds

THEOREM ClientCalledIdentitiesAlwaysFinite ==
    ASSUME ~MutEarlyReply, ~MutReadWithoutBarrier, ~MutLoseDedup, NEW ACTION Extra
    PROVE ClientSpecification(Extra) => []IsFiniteSet(CalledIds)
<1>1. RequestHistoryState => IsFiniteSet(CalledIds)
    BY FiniteCallsHaveFiniteIdentities DEF RequestHistoryState
<1> QED BY PTL, ClientHistorySourcesAlways, <1>1
=============================================================================
