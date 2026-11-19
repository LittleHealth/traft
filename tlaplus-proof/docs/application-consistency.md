# Point-store application agreement

The application maps `(series, timestamp)` to a value or absence. `Put` writes, `Delete` removes, and `Get` returns the current value or absence. Writes and deletes return success. Sequential `Effect` and `Reply` are defined in [TRaftClientCore](../models/TRaftClientCore.tla).

Ordinary writes follow timestamp, capacity, and term partition rules. Operations on the same point cannot be freely reordered within a partition. The partition invariant proves the conditions for within-partition commutativity. Reads occupy singleton partitions, separating their observations from surrounding writes.

Application requires commit knowledge supported by independent evidence and the required preceding-partition order. A replica persists its database, deduplication state, and first result together. Reapplying the same request ID returns the cached result without applying its effect again. Crash/restart preserves these records.

[TRaftApplicationAgreement](../models/TRaftApplicationAgreement.tla) connects operation-level commutativity to all reachable application histories:

- `SameAppliedSetAgreement`: equal applied sets imply equal database and durable-cache state.
- `ReadyResultsAgree`: cached results for the same request agree even at different replica progress.

Protocol `StateMachineSafety` concerns the identity of applied log entries. The application theorem additionally concerns actual store state and request results. It does not require replicas always to have identical progress or promise eventual convergence.
