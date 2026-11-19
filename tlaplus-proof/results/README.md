# Checked results

## Complete formal proof

Frozen run `20261118T174404Z` finished at 2026-11-18 22:19:37 UTC on dq-179. All **302 modules, 18,928 obligations, and 80 registered targets with their dependencies** passed from one unchanged source snapshot. Obligations were fresh (`already:false`), with final `proved` or `trivial` states.

- [Proof summary](proof-summary.json): scope, time, tool-backend counts, and resource measurements.
- [Module results](proof-modules.json): exact result hashes, expected obligations, and dependencies.
- [Target results](proof-targets.json): theorem identity and target acceptance.
- [Source verification](source-verification.json): byte-preserving publication mapping.
- [Selftests](selftests.json): parser, prover, and verifier controls.

| Final proof status/backend | Obligations |
| --- | ---: |
| smt | 4943 |
| tlapm | 13076 |
| zenon | 699 |
| ls4 | 111 |
| isabelle | 99 |

The full proof phase took 16,012.376 seconds. The sampled process-group RSS peak was 7.562 GiB under an 8 GiB cap. See [the trust boundary](../docs/trust-and-assumptions.md).

## Completed model-checking scenarios

| Class | Count | Interpretation |
| --- | ---: | --- |
| [Finite checks](completed-explorations.json) | 22 | Exploration completed for the declared constrained model or scripted scenario. |
| [Negative controls](negative-controls.json) | 20 | The designated invariant was violated by a deliberate mutation, synthetic diagnostic, or historical model/candidate. |
| [Simulation checks](completed-sampling.json) | 2 | Each specified 50-trace sample completed; a sample is not exhaustive exploration. |

The [scenario manifest](../manifests/published-checks.json) additionally includes one syntax check. Stable IDs connect configurations, parameters, results, hashes, and evidence paths. Normal protocol, candidate, application, recovery, fold-observer, and repaired-capacity checks are represented. [Counterexample classifications](../docs/counterexamples.md) distinguish protocol mutations from candidate or client-model issues.

TLC does not discharge the unbounded proof obligations. Exact source snapshots and raw logs are in [the evidence attachments](../evidence/README.md).

## Publication interface validation

The public layout and entry points were additionally checked on dq-179. [The publication report](publication-validation.json) records byte-preserving source migration, full archived-evidence verification, genuine prover controls, replay of the 45 published entries, selected proof smoke checks, verifier regression tests, and a fresh isolated tool installation. These checks validate the publication interface; the full theorem evidence is the frozen run above. Detailed machine records are under `publication-checks/`.
