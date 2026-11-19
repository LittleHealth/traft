------------------------- MODULE TRaftClientUnboundedProof ------------------------
EXTENDS TRaftClientLinearizability, TRaftUnboundedClientHistoryIdentity


THEOREM UnboundedClientSafetyIdentity == Safety <=> UnboundedClient!Safety
BY ONLY SMT, UnboundedClientCoreAliasSafety

THEOREM UnboundedClientLinearizability ==
    UnboundedClient!ClientSpec => []UnboundedClient!FoldHistoryLinearizable
BY ONLY PTL, ClientLinearizability, UnboundedClientSpecificationIdentity,
   UnboundedClientHistoryIdentity, UnboundedClientSelectors
   DEF UnboundedClientSelectors

THEOREM UnboundedApplicationAgreement ==
    UnboundedClient!ClientSpec => [](SameAppliedSetAgreement /\ ReadyResultsAgree)
<1>1. ClientSpec => [](SameAppliedSetAgreement /\ ReadyResultsAgree)
    BY ONLY ApplicationAgreement, UnboundedClientSelectors
       DEF ClientSpec, UnboundedClientSelectors
<1> QED BY ONLY PTL, <1>1, UnboundedClientSpecificationIdentity

THEOREM UnboundedClientProtocolSafety ==
    UnboundedClient!ClientSpec => []UnboundedClient!Safety
BY PTL, SharedClientProtocolRefinement, ProtocolSafety,
   UnboundedClientSpecificationIdentity, UnboundedClientSafetyIdentity
=============================================================================
