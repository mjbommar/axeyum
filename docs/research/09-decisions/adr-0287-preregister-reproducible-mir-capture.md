# ADR-0287: Preregister reproducible compiler-MIR capture and drift detection

Status: proposed
Date: 2026-07-20

Result state: zero-row; no MIR source, compiler output, checker, or test has been
added under this ADR

## Context

ADR-0286 accepts the first checked LLVM byte-memory profile and leaves MIR
writes as the next missing half of T5.1.5. The existing MIR reflector is not yet
a safe place to add that semantic slice. Its tests embed hand-copied
`-Zunpretty=mir` strings, its line parser panics on malformed or unsupported
input, and neither the source text nor the compiler identity is bound to those
strings. A passing proof therefore does not detect that a source fixture or
nightly MIR spelling has drifted away from the committed text.

T5.1.3 already names the required seam: capture a target's own compiler MIR,
retain a stable-CI fixture, and fail visibly when the fixture is stale. The
installed compiler is currently `rustc 1.97.0-nightly` at commit
`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, host
`x86_64-unknown-linux-gnu`, with LLVM 22.1.4. Its `-Zunpretty=mir` format is
explicitly unstable and human-oriented. That makes exact provenance and drift
detection prerequisites, not optional documentation.

This ADR is an enabling capture increment. It does not make the existing MIR
parser non-panicking, add writes, reflect a whole Cargo package, or complete
T5.1.3/T5.1.5.

## Decision

Add one repository-owned MIR capture package under
`crates/axeyum-verify/tests/fixtures/mir/` containing:

- an ordinary Rust library source fixture;
- the raw standard output from one exact `rustc -Zunpretty=mir` invocation;
- a machine-readable provenance manifest with the complete `rustc -vV`
  identity and ordered compiler arguments; and
- SHA-256 identities for the source, raw output, and provenance data.

The source fixture must contain named scalar control-flow, checked array-read,
clamped-read, and array store-then-load functions. The write is captured now so
the next semantic ADR can consume a real compiler artifact. Merely containing
those tokens confers no reflection or correctness claim.

Add one repository script with three explicit modes:

1. `--verify` always validates the manifest schema, paths, and all committed
   hashes. When the selected compiler has the exact registered identity, it
   also regenerates into a workspace-owned temporary directory and byte-compares
   the raw output. With a different or absent compiler it succeeds only for the
   committed-content checks and prints a stable `compiler replay: unavailable`
   status; it must never report replay success.
2. `--require-replay` performs the same checks but fails unless the exact
   compiler is present and regeneration is byte-identical. This is the local
   acceptance and pinned-nightly gate.
3. `--regenerate` refuses any compiler identity other than the registered one,
   captures to a temporary file, verifies a second capture is byte-identical,
   and then replaces only the registered raw-output and hash artifacts.

The script accepts a task-specific compiler override rather than assuming the
ambient `rustc`. It parses its data as data: no shell `source`, `eval`, or
manifest-controlled command construction is permitted. Compiler stdout is
stored byte-for-byte; stderr is reported on failure and is not folded into the
MIR fixture. There is no whitespace, path, symbol, comment, or unstable-ID
normalization.

Wire the ordinary `--verify` mode into an `axeyum-verify` integration test so
the existing Cargo test flow detects source, manifest, or output drift on
stable CI. Keep `--require-replay` as a separately named exact-toolchain gate;
do not make the workspace default toolchain nightly or add compiler-private
dependencies.

## Pre-implementation acceptance gates

Tests and captures begin only after this zero-row ADR is committed. The
implementation must then satisfy all of the following:

1. the committed manifest records the exact release, commit hash/date, host,
   LLVM version, full ordered argv, capture-stream rule, and relative paths;
2. two fresh captures with the registered compiler are byte-identical, and
   `--require-replay` proves the committed output is an exact third copy;
3. the committed output is unmodified compiler stdout and contains exactly the
   named source functions, including an array assignment followed by a read;
4. changing one byte in a copied source, output, or provenance file produces a
   distinct stable failure class before any compiler execution is credited;
5. a source change without a regenerated output fails through its committed
   source hash, so stable CI cannot silently accept an edited source with stale
   MIR;
6. a wrong compiler release, commit, host, or LLVM identity is distinguished
   from content drift: `--verify` reports replay unavailable and
   `--require-replay`/`--regenerate` fail without modifying an artifact;
7. malformed schemas, absolute or escaping paths, duplicate keys/files,
   missing files, unexpected registered files, and invalid SHA-256 values fail
   closed without executing a manifest-provided command;
8. regeneration writes only the canonical capture package, uses temporary
   files on the workspace filesystem, and leaves the prior package intact on
   compiler failure or nondeterministic output;
9. repeated successful verification emits deterministic machine-checkable
   status fields for content validity and compiler-replay availability;
10. the Cargo integration test exercises committed-content verification, while
    focused checker tests exercise tampering, wrong-compiler, malformed-data,
    and no-partial-write cases on copied fixture roots;
11. the default/MSRV/native/WASM dependency surfaces do not change, no
    `rustc_private`, `stable_mir`, Charon, or new third-party package is added,
    and no reflection result is claimed from capture alone; and
12. the focused tests, complete `axeyum-verify --all-features` suite, workspace
    formatting, strict Clippy/rustdoc, and repository link checker pass.

The gates may be strengthened before the first source or compiler-output
fixture is added. They may not be weakened after any capture or test result is
observed.

## Consequences

The subsequent checked-MIR-memory ADR can start from a reproducible compiler
artifact containing the required store/load shape instead of copying another
text sample into a test. Stable CI will detect committed fixture drift even
when the pinned nightly is unavailable, and exact-toolchain runs will prove
byte reproduction rather than inferring it from hashes.

This deliberately leaves the semantic risk visible. The current parser still
panics and assumes a bounds assertion guards every indexed read. Before a MIR
write can become a checked public path, a separate ADR must define non-panicking
syntax/reflection errors, explicit access definedness, memory joins, and
source-level witness replay. Long-term `stable_mir` integration remains a
separate dependency/trust decision.

## Alternatives

- Add MIR writes directly to the current line parser: rejected because it would
  expand semantics over hand-maintained, unauthenticated compiler text and
  preserve panic-based rejection.
- Normalize MIR before committing it: rejected because normalization could hide
  exactly the compiler spelling drift this gate exists to expose.
- Require the pinned nightly in every workspace test: rejected because the
  repository's stable/MSRV contract must remain intact; exact replay is a
  separate named gate.
- Adopt `rustc_private`, Charon, or `stable_mir` now: deferred because each
  changes the build and trust boundary and is larger than the provenance seam.

## References

- T5.1.3 and T5.1.5 in the Track 5 reflection plan.
- `docs/consumer-track/verify/real-rust-frontend.md`.
- ADR-0286.
