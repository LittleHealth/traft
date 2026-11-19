# TRaft: machine-checked proof artifact

[Download proof evidence](https://github.com/LittleHealth/traft/releases/tag/traft-proof-v1) · [Versioned proof source](https://github.com/LittleHealth/traft/tree/traft-proof-v1)

This artifact proves protocol safety, deterministic point-store agreement, and linearizability of the specified single-group client interface with logged reads.

The frozen run `20261118T174404Z` completed on **2026-11-18 at 22:19:37 UTC** on dq-179: **302/302 proof modules, 18,928/18,928 obligations, and 80/80 registered targets and their dependencies passed**. Obligations were checked afresh. TLC provides supplementary checks of explicitly bounded configurations.

## Reading path

1. [Claims and scope](docs/claims-and-scope.md): precise guarantees and assumptions.
2. [Paper correspondence](docs/paper-correspondence.md): manuscript rules, formal interpretation, and all 26 Safety properties.
3. [Proof guide](docs/proof-guide.md): the induction and refinement chain.
4. [Completed results](results/README.md): coverage and completed TLC scenarios.
5. [Reproduction](docs/reproduction.md): verify evidence, run controls, or rerun the complete proof.

Focused guides cover [the invariant](docs/invariant-guide.md), [cross-term recovery](docs/recovery-safety.md), [application agreement](docs/application-consistency.md), [client linearizability](docs/client-linearizability.md), and [counterexamples and repairs](docs/counterexamples.md).

The [revised appendix](../supplementary/README.md) states the precise recovery rule and aligns its proof sketches with this model. This 20 November 2026 documentation clarification preserves the published main paper, formal sources, and recorded checks.

## Proof entry points

| Guarantee | Entry theorem |
| --- | --- |
| Protocol Safety | `ProtocolSafety` in [TRaftProtocolSafety](models/TRaftProtocolSafety.tla), transported to [TRaftUnboundedSafetyProof](models/TRaftUnboundedSafetyProof.tla) |
| Point-store agreement | `ApplicationAgreement` in [TRaftApplicationAgreement](models/TRaftApplicationAgreement.tla) |
| Client linearizability | `ClientLinearizability` in [TRaftClientLinearizability](models/TRaftClientLinearizability.tla), transported to [TRaftClientUnboundedProof](models/TRaftClientUnboundedProof.tla) |

These conclusions concern the defined model. Logged singleton-partition reads and persistent request deduplication are client extensions. IoTDB implementation refinement, membership changes, snapshots, cross-group transactions, and liveness are outside this proof.

## Layout and resources

`models/` contains unchanged formal modules in one import directory; the [module index](docs/module-index.md) lists every module. `configs/` contains the published completed scenarios. `manifests/` connects sources, targets, dependencies, and check IDs. `results/` contains concise reports. [Evidence attachments](evidence/README.md) contain separately hashed raw records.

Execution targets Linux x86_64. The original full proof phase took about **4.45 hours**, with one proof process at a time and an **8 GiB process-group RSS limit**. TLC jobs are serial, at most 2 workers, 2 GiB heap, 60 seconds, and 0.25 GiB of state/output each. See the [trust boundary](docs/trust-and-assumptions.md).
