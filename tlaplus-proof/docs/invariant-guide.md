# The inductive invariant

Definitions are in [TRaftProofState](../models/TRaftProofState.tla) and [TRaftInvariantDefinitions](../models/TRaftInvariantDefinitions.tla). The source definitions are authoritative; this table explains their roles.

| Predicate family | Established fact | Use |
| --- | --- | --- |
| Types, finite logs, terms and votes | Valid identities, finite per-state collections, monotone promises, one vote per term | Quorum, maximum, and cardinality arguments |
| Election and control provenance | Requests, votes, certificates, and recovery phases have actual sources | Excludes fabricated elections and proposals |
| Canonical origins and shape | Entries share a creation context and coherent closed prefixes | Establishes subset relations before comparing counts |
| Boundary counts and messages | Counts and entry fields come from the actual creation context | Connects count equality to content equality |
| Durable sources and ACK provenance | ACKs follow persistence and authorized messages | Separates evidence from commit flags and notifications |
| Potential evidence and recovery | Old-term ACK possibilities are bounded and inherited | Covers certificates completed across term changes |
| Installed and closed history | Installed entries and closed-partition observations have valid complete sources | Separates retained proposals from installed histories |
| Application and evidence order | Applied entries have evidence and respect preceding partitions | Supports Safety and application agreement |

Initialization, every actual action, and stuttering are checked. Some action proofs use post-state facts established earlier in the same step; those facts have independent preservation obligations. They are not additional protocol assumptions.

The historical two-state diagnostics use artificial states admitted by older candidates. Their exclusion is useful only together with preservation of the strengthened candidate. The reachable ordinary no-op self-ACK trace instead refuted an overstrong candidate; the final candidate permits that behavior. See [counterexamples](counterexamples.md).

The observer-passivity negative control deliberately creates a nonprotocol application step. The observer must admit the step and record FALSE, checking that observation does not silently filter a violation.
