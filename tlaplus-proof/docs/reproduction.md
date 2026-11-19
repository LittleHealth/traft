# Reproducing the artifact

Run the commands below from `tlaplus-proof/`. Every execution uses a **new output directory**; existing evidence is not overwritten. Only the public completed-scenario manifest is used by the TLC entry point.

## 1. Inspect existing evidence

Obtain the attachments indexed in [evidence/release-assets.json](../evidence/release-assets.json). [The release page](https://github.com/LittleHealth/traft/releases/tag/traft-proof-v1) provides all downloads. Use the [matching tagged source checkout](https://github.com/LittleHealth/traft/tree/traft-proof-v1).

```bash
python3 scripts/artifact.py verify
python3 scripts/artifact.py verify --assets /path/to/release-assets --report /tmp/traft-evidence-verification.json
```

The first command checks the byte-preserved source mapping. The second additionally streams and hashes every archive member, validates all registered proof obligations/dependencies and target identities, and matches each published TLC result to its model, configuration, and source hashes. It does not rerun TLAPS or TLC.

## 2. Install the pinned toolchain

Requirements: Linux x86_64; Python 3.10 or later; Java 11 or later; curl, gpgv, dpkg-deb; and the Ubuntu archive keyring at `/usr/share/keyrings/ubuntu-archive-keyring.gpg`. Installation uses an isolated directory and private compatibility runtime. The frozen tool versions are in [toolchain-lock.json](../toolchain/toolchain-lock.json).

```bash
python3 scripts/bootstrap.py --output /tmp/traft-review-tools
```

Optional `--asset-cache` and `--libc-cache` arguments reuse downloaded official TLAPM and libc packages only after checksum verification. Use the separately supplied, hash-pinned `tla2tools.jar`; an arbitrary newer JAR is rejected. An existing installation can be reused by passing its unchanged `toolchain.json` below.

## 3. Check controls and bounded scenarios

```bash
python3 scripts/artifact.py selftest --jar /path/to/tla2tools.jar --toolchain /tmp/traft-review-tools/toolchain.json --output /tmp/traft-review-selftest
python3 scripts/artifact.py tlc --list
python3 scripts/artifact.py tlc --jar /path/to/tla2tools.jar --check protocol-tlc--recovery --output /tmp/traft-review-recovery
python3 scripts/artifact.py tlc --jar /path/to/tla2tools.jar --output /tmp/traft-review-completed-suite
python3 scripts/artifact.py check-results --run /tmp/traft-review-completed-suite
```

`selftest` checks the frozen acceptance parser, genuine positive/negative prover obligations, verifier rejection of corrupt coverage, and observer/UNION TLC probes. Add `--group` to run the original grouped-prover controls too. `tlc --check` can be repeated for several stable IDs; omitting it runs all 45 manifest entries serially. Each entry retains its original resource bounds (at most 2 workers, 2 GiB heap, 60 seconds, and 0.25 GiB output). Seeds and trace counts are fixed for the two samples.

The capacity regression stages the declared historical client-core override in a fresh directory. All other current formal proofs use the current core. Negative-control acceptance requires the named violated invariant. Unexpected termination or an unmatched outcome makes the command fail, with its local output preserved for diagnosis.

## 4. Rerun formal proofs

```bash
python3 scripts/artifact.py prove --jar /path/to/tla2tools.jar --toolchain /tmp/traft-review-tools/toolchain.json --output /tmp/traft-review-full-proof
python3 scripts/artifact.py check-results --run /tmp/traft-review-full-proof
```

This runs controls and SANY preflights, then every registered module in a fresh prover process. Acceptance requires 302 modules, 18,928 obligations, 80 targets and all theorem dependencies, matching frozen source inputs, final proved/trivial states, no cached obligations, and unchanged audited tools. It never accepts a module solely from its process exit code.

For a small installation check, add `--modules TRaftFunctionProof TRaftQuorumProof` and choose a different output directory. The resulting report explicitly says `full_chain: false` and lists any dependency modules not executed. A selected proof run is not the complete proof.

The reference full run took about 4.45 hours. Proofs are serial with at most two logical cores and an 8 GiB process-group RSS cap. Allow the virtual reservations described in [the trust boundary](trust-and-assumptions.md). Each backend has a limit of at most 60 seconds; longer module budgets include normalization. Fresh runs retain their own results even if they do not match the reference run.

## Publication provenance

The [path map](../manifests/source-path-map.json) records migration from frozen input names to public names without changing their bytes. Public wrappers, reports, and English documentation are separate publication artifacts. The original full proof remains the source of the theorem claims; a publication smoke test does not replace it. Validation records identify which commands were actually replayed on dq-179.

The [publication validation](../results/publication-validation.json) records the actual dq-179 checks of these entry points, including a fresh install from the pinned caches. Verification has been exercised in that Linux environment. Other installations must satisfy the stated tool and platform requirements.

The [20 November appendix clarification](../../supplementary/README.md) changes documentation and the appendix pages of the supplementary PDF. The original main-paper pages, formal sources, execution scripts, evidence attachments, and published completed scenarios are unchanged. The [revision record](../../supplementary/appendix-revision.json) identifies the updated appendix and PDF. Original validation records remain records of their dated runs; no new TLAPS or TLC execution is claimed for this documentation revision.
