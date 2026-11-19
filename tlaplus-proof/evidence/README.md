# Raw evidence attachments

[release-assets.json](release-assets.json) records attachment names, sizes, hashes, and publication status. [Download the versioned release](https://github.com/LittleHealth/traft/releases/tag/traft-proof-v1). The release tag identifies the matching [source snapshot](https://github.com/LittleHealth/traft/tree/traft-proof-v1/tlaplus-proof).

| Attachment | Contents |
| --- | --- |
| [traft-tlaps-evidence.tar.gz](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/traft-tlaps-evidence.tar.gz) | All registered formal proof runs, individual obligation states and raw logs, source snapshots, syntax preflights, prover controls, and original tool/source audits. |
| [traft-tlc-completed-evidence.tar.gz](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/traft-tlc-completed-evidence.tar.gz) | All checks in the published completed-scenario manifest, with their original input snapshots, logs, results, and available traces. |
| [evidence-manifest.json](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/evidence-manifest.json) | Exact member hashes for both evidence archives. |
| [tla2tools.jar](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/tla2tools.jar) | The unchanged pinned TLC/SANY tool used by the recorded checks. |

[Download SHA256SUMS](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/SHA256SUMS) and the [asset index](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/release-assets.json) alongside the attachments.

Each evidence archive also contains its own [evidence-manifest.json](https://github.com/LittleHealth/traft/releases/download/traft-proof-v1/evidence-manifest.json). Selected result and log bytes are unchanged; the attachments have new hashes and explicitly named scopes. Repeated per-run source snapshots are intentionally retained. Formal proof logs include backend attempts as well as final successful obligation states.

Download the attachments into a directory and run `python3 scripts/artifact.py verify --assets /path/to/assets` from the proof package. Verification streams the archives without unpacking them, rejects duplicate/unsafe members, checks all member hashes, and checks every registered obligation and dependency. It also verifies the published scenarios' model, configuration, and source identity. See [reproduction](../docs/reproduction.md).

The maintainer exporter is [export_public_results.py](../scripts/export_public_results.py). It reads the internal frozen archive without modifying it and copies the explicitly indexed evidence byte-for-byte. It is not required for reviewers to reproduce a proof or check a downloaded attachment.
