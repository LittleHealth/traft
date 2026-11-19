---------------------- MODULE TRaftClientAdmissionProof ----------------------
EXTENDS TRaftClientCore, TLAPS

\* A full partition opens the next partition for the arriving command,
\* as in the paper's partition-index recurrence. This is a local rule,
\* independent of the protocol Safety predicate and proof history.
THEOREM CapacityBoundaryStartsSuccessor ==
    ASSUME NEW r, NEW q, q \in calls,
           Count(formal[r], Cur(formal[r])) = MaxPartitionSize
    PROVE Admit(r, q) <=>
          (CreateSuccessor(r, q, "data") /\ UNCHANGED localClientVars)
<1>1. q \in calls /\ Count(formal[r], Cur(formal[r])) = MaxPartitionSize
    OBVIOUS
<1> QED BY ONLY SMT, <1>1 DEF Admit, MustSeparate

\* Preserve the previous admission rule explicitly, including its missing
\* size-boundary branch, to check that the repair adds possible behavior.
LegacyMustSeparate(L, q) ==
    q.op = "Get" \/ HasRead(L) \/ Timestamp(q) <= MaxTimestamp(L)
LegacyAdmit(r, q) ==
    /\ q \in calls
    /\ IF LegacyMustSeparate(formal[r], q)
          THEN CreateSuccessor(r, q, "data")
          ELSE /\ Count(formal[r], Cur(formal[r])) < MaxPartitionSize
               /\ CreateEntry(r, q)
    /\ UNCHANGED localClientVars

THEOREM ExistingAdmissionsArePreserved ==
    \A r, q : LegacyAdmit(r, q) => Admit(r, q)
BY ONLY SMT, ParameterAssumptions
   DEF LegacyAdmit, LegacyMustSeparate, Admit, MustSeparate, ParameterAssumptions
=============================================================================
