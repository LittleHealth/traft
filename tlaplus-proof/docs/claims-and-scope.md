# Claims and scope

| Layer | Formal conclusion | Meaning |
| --- | --- | --- |
| Protocol | `Spec => []Safety` | Every reachable state satisfies all 26 protocol and independent-evidence safety properties. |
| Unbounded protocol | `UnboundedProtocolSafety` | Arbitrary finite fixed membership of at least three replicas, positive partition capacity, and no fixed bound on terms, indices, or execution length. |
| Point-store application | `ClientSpec => [](SameAppliedSetAgreement /\ ReadyResultsAgree)` | Equal applied-entry sets give equal stores and durable caches; cached results for the same request agree across replicas at different progress. |
| Client | `ClientSpec => []FoldHistoryLinearizable` | Every finite reachable call/return history has a legal sequential completion respecting real-time precedence. |

All entry points and dependencies are in [the proof manifest](../manifests/proof-obligations.json); [the target report](../results/proof-targets.json) records acceptance of 80 targets. Counts alone are not theorem statements.

## Model assumptions

Membership is finite and fixed. Replicas obey the protocol. Modeled durable updates are atomic and survive crashes; storage corruption is not modeled. Messages may be delayed, duplicated, or never delivered. No fairness assumption promises eventual completion. Fault-injection switches are disabled in formal theorems.

Client keys are `(series, timestamp)`, with natural-number timestamps. Operations are `Put`, `Delete`, and `Get`. Request IDs `(clientId, sequence)` cannot be reused for different commands; retries preserve ID and payload. Each logical client has at most one outstanding request. A logged `Get` occupies its own partition. Database, request deduplication, and first results are durable together.

## Boundaries

Application agreement concerns the point-store operations whose within-partition commutativity is proved. It is not a theorem for arbitrary noncommuting state machines. Linearizability belongs to this client extension, not to an unspecified paper API, unlogged reads, range queries, or multi-key transactions.

This artifact does not prove IoTDB implementation refinement, dynamic membership, snapshots/garbage collection, cross-group transactions, Byzantine tolerance, storage integrity, liveness, or eventual convergence. It does not claim strong linearizability. Current finite and proof models share the fold observer; no unbounded equivalence theorem for the historical recursive observer is claimed.

[Completed TLC scenarios](../results/README.md) corroborate selected behaviors and detect deliberate mutations. The unbounded conclusion comes from TLAPS induction and refinement.
