# Maestro device-ID capture

This directory owns the Axeyum-authored registration and, after the frozen
ADR-0323 gate runs, its metadata-only capture result. The selected external
population is Maestro's `major`, `minor`, and `makedev` at revision
`650a3f62c386d113b4cbbc11645d945d57620cbb`.

No Maestro source, LLVM, bitcode, generated replay harness, or Cargo build
product belongs in this directory. Those bytes remain under ignored `target/`
storage. The committed JSON identifies them by hashes and sizes only.

The first official result is negative: both isolated builds completed, but the
full LLVM modules differed in size and hash. The gate stopped before extraction
or parser admission and atomic cleanup retained no target byte. See
`capture-result.json`; this is not a verification or scoreboard result.

ADR-0324's separately registered follow-up is diagnostic only. It reproduces
the two modules under local ignored storage, retains a complete diff, classifies
every changed line, and compares the selected function projections. Its result
cannot revise ADR-0323 or grant capture credit.

That diagnostic identifies a build-protocol root leak: the trailing rustc
remap applies to the final kernel crate, while seven absolute paths from the
`utils` dependency remain in each module and cascade into symbol/metadata
identity. All three selected functions pass the scalar parser, but all three
mangled names and current canonical hashes differ. `drift-result.json` records
the metadata-only result; the external bytes remain local and ignored.

ADR-0325 registers a fresh v2 producer rather than modifying v1. It applies the
same remap through Cargo-encoded target flags to every dependency, requires
zero real-root tokens and raw full-module equality, and only then allows
dynamic symbol discovery and scalar parser admission. It still runs no proof.

The v2 result is negative: real-root tokens fall to zero, but the modules still
differ in size and hash, so the root-specific remap rule itself remains an
identity input. No extraction ran and no v2 artifact survived atomic cleanup.

Build the Axeyum admission probe under the standing memory cap, prepare the
locked Cargo cache if necessary, then run:

```sh
python3 scripts/capture-maestro-device-id.py --prepare-cache
```

The command refuses an existing output, validates every registered source and
tool identity, uses two isolated source roots, and writes the local result
atomically to `target/maestro-device-id-20260721/capture/`. Capture and parser
admission are not verification results; T5.5.3 requires a separate zero-row ADR
before any inverse-property query or scoreboard measurement.
