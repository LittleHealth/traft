---------------------- MODULE TRaftUnboundedCoreAliases08b ----------------------
EXTENDS TRaftUnboundedCoreAliases08

\* Continuation of the same checked definition identities; no new assumption.

THEOREM UnboundedCoreAliasEvidence ==
    \A aliasArg1 : UnboundedCore!Evidence(aliasArg1) = Evidence(aliasArg1)
BY ONLY ZenonT(10), UnboundedCoreAliasTerms
   DEF Evidence, UnboundedCore!Evidence, Quorum, UnboundedCore!Quorum,
       MessageAckers, UnboundedCore!MessageAckers,
       Cardinality, UnboundedCore!Cardinality, IsFiniteSet, UnboundedCore!IsFiniteSet

THEOREM UnboundedCoreAliasObserve ==
    UnboundedCore!Observe = Observe
<1>1. UnboundedCore!Evidence(ackMessages') = Evidence(ackMessages')
    BY ONLY UnboundedCoreAliasEvidence
<1> QED BY ONLY IsaM("auto"), <1>1, UnboundedCoreAliasTerms, UnboundedCoreAliasPartitions
   DEF Observe, UnboundedCore!Observe, Cur, UnboundedCore!Cur, MaxOr, UnboundedCore!MaxOr,
       Part, UnboundedCore!Part, Prefix, UnboundedCore!Prefix

THEOREM UnboundedCoreAliasNext ==
    UnboundedCore!Next = Next
BY ONLY SMT, UnboundedCoreAliasProtocolNext, UnboundedCoreAliasObserve
   DEF Next, UnboundedCore!Next

THEOREM UnboundedCoreAliasTypeOK ==
    UnboundedCore!TypeOK = TypeOK
BY ONLY ZenonT(10), UnboundedCoreAliasNoNode, UnboundedCoreAliasNoProposal, UnboundedCoreAliasNoReport, UnboundedCoreAliasRoles, UnboundedCoreAliasPhases, UnboundedCoreAliasTerms, UnboundedCoreAliasEntries, UnboundedCoreAliasProposalRecords, UnboundedCoreAliasCur, UnboundedCoreAliasLastIndex, UnboundedCoreAliasCount, UnboundedCoreAliasCoherent, UnboundedCoreAliasResult
   DEF TypeOK, UnboundedCore!TypeOK

THEOREM UnboundedCoreAliasElectionSafety ==
    UnboundedCore!ElectionSafety = ElectionSafety
BY ONLY ZenonT(10)
   DEF ElectionSafety, UnboundedCore!ElectionSafety
=============================================================================
