# Submission and complete paper versions

| Version | PDF pages | Contents | Download |
| --- | ---: | --- | --- |
| [Submission version](paper.pdf) | 14 | 12 pages of main text, followed by the AI acknowledgment and references on pages 13–14; no appendices | [Download submission PDF](https://raw.githubusercontent.com/LittleHealth/traft/refs/tags/traft-proof-v1/supplementary/paper.pdf) |
| [Complete version](appendix.pdf) | 18 | The same main paper, acknowledgment, and references, followed by the revised appendices from page 15 | [Download complete PDF](https://raw.githubusercontent.com/LittleHealth/traft/refs/tags/traft-proof-v1/supplementary/appendix.pdf) |

The submission PDF preserves the complete version's first 14 pages without re-typesetting or changing their text. References to appendices link to the complete PDF. [Version details and SHA256 hashes](paper-versions.json) record the page selection and verification. The complete PDF is unchanged from the 20 November publication.

- [Revised appendix LaTeX source](appendix-body.tex).
- [Revision provenance and SHA256 hashes](appendix-revision.json).
- [Paper, model, and theorem correspondence](../tlaplus-proof/docs/paper-correspondence.md).

The 20 November 2026 clarification appears in Appendix A, beginning on PDF page 15. It defines selection of the latest complete durable recovery result, the creation-term and partition conditions for merging reported extensions, and persistence before recovery acknowledgment. The Log Matching and Leader Completeness sketches distinguish ordinary partition advancement from recovery proposal confirmation. No pseudocode was added.

The complete PDF contains 18 pages. Its first 14 pages are copied from the originally published PDF, preserving their content streams and extracted text. Only the appendix pages were replaced in the 20 November clarification. The manuscript body and the frozen TLA+ model are unchanged.

`appendix-body.tex` is the revised manuscript input fragment, not a standalone LaTeX project. It uses the manuscript preamble, cross-references, and other appendix inputs. The PDF provides the complete rendered document.

The [frozen source audit](../tlaplus-proof/results/source-verification.json) records the original publication, including its earlier appendix and PDF hashes. It is retained as historical evidence. The revision record above identifies the current appendix and PDF; it does not replace or reinterpret the original proof run. Formal sources, proof results, evidence attachments, and the completed TLC scenario manifest are unchanged.
