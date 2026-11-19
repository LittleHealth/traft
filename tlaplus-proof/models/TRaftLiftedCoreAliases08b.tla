---------------------- MODULE TRaftLiftedCoreAliases08b ----------------------
EXTENDS TRaftLiftedCoreAliases08

\* Continuation of the same checked definition identities; no new assumption.

THEOREM LiftedCoreAliasEvidence ==
    \A aliasArg1 : LiftedSafety!Evidence(aliasArg1) = Evidence(aliasArg1)
BY ONLY ZenonT(10), LiftedCoreAliasTerms
   DEF Evidence, LiftedSafety!Evidence, Quorum, LiftedSafety!Quorum,
       MessageAckers, LiftedSafety!MessageAckers,
       Cardinality, LiftedSafety!Cardinality, IsFiniteSet, LiftedSafety!IsFiniteSet

THEOREM LiftedCoreAliasObserve ==
    LiftedSafety!Observe = Observe
<1>1. LiftedSafety!Evidence(ackMessages') = Evidence(ackMessages')
    BY ONLY LiftedCoreAliasEvidence
<1> QED BY ONLY IsaM("auto"), <1>1, LiftedCoreAliasTerms, LiftedCoreAliasPartitions
   DEF Observe, LiftedSafety!Observe, Cur, LiftedSafety!Cur, MaxOr, LiftedSafety!MaxOr,
       Part, LiftedSafety!Part, Prefix, LiftedSafety!Prefix

THEOREM LiftedCoreAliasNext ==
    LiftedSafety!Next = Next
BY ONLY SMT, LiftedCoreAliasProtocolNext, LiftedCoreAliasObserve
   DEF Next, LiftedSafety!Next

THEOREM LiftedCoreAliasTypeOK ==
    LiftedSafety!TypeOK = TypeOK
BY ONLY ZenonT(10), LiftedCoreAliasNoNode, LiftedCoreAliasNoProposal, LiftedCoreAliasNoReport, LiftedCoreAliasRoles, LiftedCoreAliasPhases, LiftedCoreAliasTerms, LiftedCoreAliasEntries, LiftedCoreAliasProposalRecords, LiftedCoreAliasCur, LiftedCoreAliasLastIndex, LiftedCoreAliasCount, LiftedCoreAliasCoherent, LiftedCoreAliasResult
   DEF TypeOK, LiftedSafety!TypeOK

THEOREM LiftedCoreAliasElectionSafety ==
    LiftedSafety!ElectionSafety = ElectionSafety
BY ONLY ZenonT(10)
   DEF ElectionSafety, LiftedSafety!ElectionSafety
=============================================================================
