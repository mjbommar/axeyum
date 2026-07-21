# Maestro device-ID capture

This directory owns the Axeyum-authored registration and, after the frozen
ADR-0323 gate runs, its metadata-only capture result. The selected external
population is Maestro's `major`, `minor`, and `makedev` at revision
`650a3f62c386d113b4cbbc11645d945d57620cbb`.

No Maestro source, LLVM, bitcode, generated replay harness, or Cargo build
product belongs in this directory. Those bytes remain under ignored `target/`
storage. The committed JSON identifies them by hashes and sizes only.

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
