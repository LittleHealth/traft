---------------------- MODULE TRaftUnboundedClientCoreAliases08b ----------------------
EXTENDS TRaftUnboundedClientCoreAliases08

\* Continuation of the same checked definition identities; no new assumption.

THEOREM UnboundedClientCoreAliasEvidence ==
    \A aliasArg1 : UnboundedClient!Evidence(aliasArg1) = Evidence(aliasArg1)
BY ONLY ZenonT(10), UnboundedClientCoreAliasTerms
   DEF Evidence, UnboundedClient!Evidence, Quorum, UnboundedClient!Quorum,
       MessageAckers, UnboundedClient!MessageAckers,
       Cardinality, UnboundedClient!Cardinality, IsFiniteSet, UnboundedClient!IsFiniteSet

THEOREM UnboundedClientCoreAliasObserve ==
    UnboundedClient!Observe = Observe
<1>1. UnboundedClient!Evidence(ackMessages') = Evidence(ackMessages')
    BY ONLY UnboundedClientCoreAliasEvidence
<1> QED BY ONLY IsaM("auto"), <1>1, UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasPartitions
   DEF Observe, UnboundedClient!Observe, Cur, UnboundedClient!Cur, MaxOr, UnboundedClient!MaxOr,
       Part, UnboundedClient!Part, Prefix, UnboundedClient!Prefix

THEOREM UnboundedClientCoreAliasNext ==
    UnboundedClient!Next = Next
BY ONLY SMT, UnboundedClientCoreAliasProtocolNext, UnboundedClientCoreAliasObserve
   DEF Next, UnboundedClient!Next

THEOREM UnboundedClientCoreAliasTypeOK ==
    UnboundedClient!TypeOK = TypeOK
BY ONLY ZenonT(10), UnboundedClientCoreAliasNoNode, UnboundedClientCoreAliasNoProposal, UnboundedClientCoreAliasNoReport, UnboundedClientCoreAliasRoles, UnboundedClientCoreAliasPhases, UnboundedClientCoreAliasTerms, UnboundedClientCoreAliasEntries, UnboundedClientCoreAliasProposalRecords, UnboundedClientCoreAliasCur, UnboundedClientCoreAliasLastIndex, UnboundedClientCoreAliasCount, UnboundedClientCoreAliasCoherent, UnboundedClientCoreAliasResult
   DEF TypeOK, UnboundedClient!TypeOK

THEOREM UnboundedClientCoreAliasElectionSafety ==
    UnboundedClient!ElectionSafety = ElectionSafety
BY ONLY ZenonT(10)
   DEF ElectionSafety, UnboundedClient!ElectionSafety
=============================================================================
