# Pinned toolchain

[toolchain-lock.json](toolchain-lock.json) records the exact official TLAPM package, compatibility runtime, and TLC/SANY JAR. The JAR is supplied as a separately hashed attachment because an evolving upstream development download would not identify this build.

The installer preserves official executables and adds recorded private-runtime wrappers. It verifies the Ubuntu package against the supplied signed metadata using the installed Ubuntu archive keyring. System libraries are not modified.

Use [the public bootstrap wrapper](../scripts/bootstrap.py) in a new output directory. It stages the byte-preserved installer and pinned runtime metadata. See [reproduction](../docs/reproduction.md) for prerequisites, commands, and resource limits. An installation record is not a proof result.
