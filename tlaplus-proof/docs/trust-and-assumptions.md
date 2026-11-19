# Assumptions and trust boundary

The theorem applies to the interpretation in [paper correspondence](paper-correspondence.md), with the assumptions in [claims and scope](claims-and-scope.md). Connecting concrete implementation code to this model is a separate obligation.

The official TLAPM 1.6 prerelease is version `bf665f4`, commit `bf665f4d162c1ae5010ca878578cd50a810ec205`. Package, executable, libraries, backends, wrappers, and isolated compatibility runtime have recorded hashes. Backends include Z3 4.8.9, Zenon 0.8.4, LS4, and Isabelle2025 with Poly/ML 5.9.1. Official ELF bytes are unchanged.

The trust boundary includes TLA+ semantics, model correspondence, TLAPM parsing and obligation generation, its standard library, invoked backends, runtime/OS, and execution/acceptance scripts. **Not every SMT result is independently replayed through an Isabelle small kernel.** TLAPM's `trivial` obligations are reported separately from backend counts.

Installation extracts private glibc 2.39 from a pinned package checked against signed Ubuntu metadata. It does not replace system libraries or execute package scripts. Requirements: Linux x86_64, Python 3, curl, gpgv, dpkg-deb, Ubuntu archive keyring, and Java 11 or later. The original host used Java 11.0.28 and Python 3.10.12.

Proofs run serially, one prover thread, at most two logical cores. Process-group RSS is limited to 8 GiB; original sampled peak was 7.562 GiB. Address-space reservations are 16 GiB for the main profile and 32 GiB for Poly/ML. Backend limits are at most 60 seconds; the original formal run requested at most 30 seconds. Module limits of 300/900/1800 seconds include parsing and normalization.

TLC jobs use at most two workers, 2 GiB heap, 20–60 seconds, and 0.25 GiB state/output. Negative controls require the designated violation and are not positive Safety passes. Acceptance checks input hashes, individual statuses, counts, and dependency closure separately from exit codes.
