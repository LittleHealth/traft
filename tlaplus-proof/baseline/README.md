# Historical sources for completed regression checks

These byte-preserved files support source provenance and explicit regression cases. They are not used by the current formal target proofs.

The capacity-one negative control overrides only `TRaftClientCore.tla` with `TRaftClientCore-before-shared-observer.tla` in a fresh workspace. Its paired positive control uses the current core. The exact override is declared in [published-checks.json](../manifests/published-checks.json).

`TRaftCore-before-continuation.tla`, `TRaftClients-before-shared-observer.tla`, and the historical `TRaftPaper.tla` retain the source baselines used in the original audit. See [counterexamples](../docs/counterexamples.md) for their scope.
