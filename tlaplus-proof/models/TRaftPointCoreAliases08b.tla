---------------------- MODULE TRaftPointCoreAliases08b ----------------------
EXTENDS TRaftPointCoreAliases08

\* Continuation of the same checked definition identities; no new assumption.

THEOREM PointCoreAliasEvidence ==
    \A aliasArg1 : PointLift!Evidence(aliasArg1) = Evidence(aliasArg1)
BY ONLY ZenonT(10), PointCoreAliasTerms
   DEF Evidence, PointLift!Evidence, Quorum, PointLift!Quorum,
       MessageAckers, PointLift!MessageAckers,
       Cardinality, PointLift!Cardinality, IsFiniteSet, PointLift!IsFiniteSet

THEOREM PointCoreAliasObserve ==
    PointLift!Observe = Observe
<1>1. PointLift!Evidence(ackMessages') = Evidence(ackMessages')
    BY ONLY PointCoreAliasEvidence
<1> QED BY ONLY IsaM("auto"), <1>1, PointCoreAliasTerms, PointCoreAliasPartitions
   DEF Observe, PointLift!Observe, Cur, PointLift!Cur, MaxOr, PointLift!MaxOr,
       Part, PointLift!Part, Prefix, PointLift!Prefix

THEOREM PointCoreAliasNext ==
    PointLift!Next = Next
BY ONLY SMT, PointCoreAliasProtocolNext, PointCoreAliasObserve
   DEF Next, PointLift!Next

THEOREM PointCoreAliasTypeOK ==
    PointLift!TypeOK = TypeOK
BY ONLY ZenonT(10), PointCoreAliasNoNode, PointCoreAliasNoProposal, PointCoreAliasNoReport, PointCoreAliasRoles, PointCoreAliasPhases, PointCoreAliasTerms, PointCoreAliasEntries, PointCoreAliasProposalRecords, PointCoreAliasCur, PointCoreAliasLastIndex, PointCoreAliasCount, PointCoreAliasCoherent, PointCoreAliasResult
   DEF TypeOK, PointLift!TypeOK

THEOREM PointCoreAliasElectionSafety ==
    PointLift!ElectionSafety = ElectionSafety
BY ONLY ZenonT(10)
   DEF ElectionSafety, PointLift!ElectionSafety
=============================================================================
