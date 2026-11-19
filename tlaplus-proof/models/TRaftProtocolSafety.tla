---------------------- MODULE TRaftProtocolSafety ----------------------
EXTENDS TRaftLiftedSafetyTransport

\* One part of the original protocol transport proof. Every dependency
\* must pass its own frozen-source check; no safety premise is added.

THEOREM ProtocolInvariant == Spec => []LiftedSafety!Inv
BY ONLY PTL, CoreAndHistoryRefinement, LiftedInvariantWithoutFreeHistory

THEOREM ProtocolSafety == Spec => []Safety
BY ONLY PTL, CoreAndHistoryRefinement, LiftedSafetyWithoutFreeHistory
=============================================================================
