# Linearizability of the logged point interface

## Interface

`Put`, `Delete`, and `Get` operate within one consensus group. Keys are `(series, timestamp)`. Request IDs `(clientId, sequence)` are nonreusable; retries preserve ID and payload. Each logical client has at most one outstanding request.

A `Get` is the only entry in its partition. Its result is obtained when committed and applied; later entries use the next partition. The database, deduplication records, and first reply are durable together. Timeout or response loss leaves a pending request, not proof of no effect. Retries return the original result; late responses are matched by request identity.

## Independent history specification

`FoldHistoryLinearizable` is a predicate on invocation/response history and the sequential point-store specification. It does not define correctness using implementation ACK evidence. Evidence constructs a witness that satisfies the independent history predicate.

The witness extends at first formation of independent commit evidence. When recovery certifies multiple entries at once, they are ordered by index consistently with partition order. Request IDs are deduplicated in the fold. The application proof connects each cached response to the same abstract effect or read result.

Completed operations appear with their actual results. If a response precedes another invocation, the witness preserves that order. Pending invocations may be completed in the abstract history; this is a safety construction, not an eventual-response guarantee.

## Final theorem

[TRaftClientLinearizability](../models/TRaftClientLinearizability.tla) proves `ClientSpec => []FoldHistoryLinearizable`. [TRaftClientUnboundedProof](../models/TRaftClientUnboundedProof.tla) transports it through the checked specification and history identities. Every finite reachable history prefix of the unbounded model is linearizable.

This client extension does not establish linearizability for an undefined paper interface, unlogged reads, range queries, or IoTDB code. Strong linearizability and unbounded equivalence to the older recursive observer are not claimed.

Completed scenarios cover point operations, concurrent overwrites, response loss, durable deduplication after restart, and cross-term retries. Negative controls detect early replies, bypassed read barriers, and lost deduplication state.
