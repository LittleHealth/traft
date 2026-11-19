# TRaft supplementary material

[Download proof evidence](https://github.com/LittleHealth/traft/releases/tag/traft-proof-v1) · [Versioned source](https://github.com/LittleHealth/traft/tree/traft-proof-v1)

TRaft: Towards Strong Consistency via Out-of-order Separation for IoT Workloads.

- [Submission PDF: 12 pages of main text plus acknowledgment and references, 14 pages total](supplementary/paper.pdf).
- [Complete paper with appendices: 18 pages](supplementary/appendix.pdf).
- [Revised appendix source and provenance](supplementary/README.md).
- [Machine-checked TLA+ proof artifact](tlaplus-proof/README.md).
- [Performance experiment instructions](reproducibility/README.md).
- [IoTDB implementation branch](https://github.com/apache/iotdb/tree/research/traft).

The frozen proof run completed on **18 November 2026 (UTC)**: **302 proof modules, 18,928 obligations, and 80 target theorems with their dependencies passed**. The protocol proof covers all 26 Safety components and cross-term recovery. Application agreement and linearizability concern the specified single-group point-store extension with logged reads and durable deduplication; they do not establish refinement of the IoTDB implementation.

Start with [claims and scope](tlaplus-proof/docs/claims-and-scope.md), [paper correspondence](tlaplus-proof/docs/paper-correspondence.md), and [the proof guide](tlaplus-proof/docs/proof-guide.md). [Completed TLC scenarios](tlaplus-proof/results/README.md) provide supplementary evidence. See [reproduction](tlaplus-proof/docs/reproduction.md) for independent checks.

The appendix was clarified on 20 November 2026 to state the recovery merge rule and align the proof sketches with the frozen model. The PDF preserves the original published main paper (pages 1–14) and replaces only its appendix pages. Formal sources and the published completed TLC checks are unchanged. [Revision provenance](supplementary/appendix-revision.json) records the checks and hashes. [Citation metadata](CITATION.cff) identifies the artifact; cite the exact commit or released version reviewed.
