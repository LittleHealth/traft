# Counterexamples and repairs

These completed diagnostics document what earlier models or candidates admitted. The final frozen run checks the corrected candidate, current client model, and complete theorem dependency chain. [The result index](../results/negative-controls.json) identifies exact raw results and failed invariants.

| Class | Cases | Meaning and repair |
| --- | --- | --- |
| Artificial induction countermodels | Nine two-state traces | Older candidates admitted unsupported votes, messages, counts, activation/application/context histories, partial closed histories, unordered evidence, or uncertified installed recovery history. Proven source, completeness, and ordering invariants exclude these pre-states. They are not executions from protocol Init. |
| Reachable overstrong candidate | Ordinary no-op self-ACK, 25 states | A normal boundary no-op can receive a single-entry self-ACK without a commit certificate. The old candidate demanded too much prefix evidence. The corrected candidate permits the trace while preserving all 26 Safety properties. |
| Client admission omission | Old capacity-one failure at 32 states; repaired scenario 79 states | Restoring the paper's capacity branch adds permitted behavior. The old trace refutes `FirstWriteEnabled`, not protocol Safety. Formal proofs cover the repaired client model. |
| Observer passivity | Two-state synthetic application step | A deliberately nonprotocol application must be admitted by the observer and recorded as FALSE, producing `NoRecordedOrderViolation`. |
| Protocol mutations | Five controls | Removing quorum evidence, skipping preceding-partition commitment, early recovery publication, dropping pending proposals, and skipping the union trigger their designated checks. |
| Client mutations | Three controls | Early replies, unlogged reads, and forgotten deduplication trigger `HistoryLinearizable`. |

The [scenario manifest](../manifests/published-checks.json) identifies each case. The 25- and 32-state lengths refer to preserved scenarios, not claims of globally shortest counterexamples.

Before the final freeze, source repairs also made UNION operand grouping explicit, corrected observer assignment grouping, and supplied local function-domain/source premises from established invariants. No Safety component was removed and no global Safety/Inv guard was added to protocol actions.

[Historical sources](../baseline/README.md) are used only by explicit regression scenarios. Formal target proofs use the current frozen sources with fault-injection flags disabled.
