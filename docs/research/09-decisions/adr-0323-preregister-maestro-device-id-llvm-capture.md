# ADR-0323: Preregister Maestro device-ID LLVM capture

Status: proposed
Date: 2026-07-21

## Context

P5.5 T5.5.1 selects Maestro's `kernel::device::id::{major, minor,
makedev}` functions as Axeyum's first measured external target. The exact
[selection note](../../plan/track-5-verified-systems/P5.5-target-selection-maestro-device-id.md)
records why this is the smallest useful target among Maestro, Tock, Hubris,
rust-sel4, and Asterinas OSTD. The three functions are used by real kernel
device, initramfs, filesystem-syscall, and `stat` paths, but compile to
single-block scalar LLVM that should require no new operator semantics.

A disposable feasibility build at the selected revision emitted all three
definitions from Maestro's own locked kernel build. That observation selected
the capture experiment only. Its bytes and timing are not retained evidence,
and no parser or solver result has been observed. T5.5.2 must now establish a
reproducible external-artifact boundary before T5.5.3 can measure the universal
inverse properties.

The target source declares GPL-3.0-or-later terms while Axeyum is MIT OR
Apache-2.0. This ADR does not decide license compatibility. It instead freezes
a conservative operational boundary: no Maestro source or compiler-derived
artifact is committed until a separate distribution and attribution review is
recorded.

## Decision

Add an Axeyum-owned local capture tool,
`scripts/capture-maestro-device-id.py`, plus a registration and result manifest
under `bench-results/verify-maestro-device-id-20260721/`. The tool validates an
existing local Maestro Git object store, expands the selected tree into two
independent temporary roots, builds the complete kernel LLVM module twice,
extracts exactly the three selected functions, checks their syntax through the
existing typed LLVM front end, and writes results atomically under ignored
`target/` storage.

Only Axeyum-owned code, commands, hashes, provenance metadata, and reports may
be committed. The source trees, full modules, extracted modules, generated host
replay harnesses, bitcode, and Cargo build trees stay local and ignored. A
committed result manifest may identify those bytes by size and SHA-256 without
including them.

## Frozen registration

The external identity is:

- repository: `https://github.com/maestro-os/maestro.git`;
- commit: `650a3f62c386d113b4cbbc11645d945d57620cbb`;
- tree: `6a51753d1f7b80117979db4f35146f55f5e248b4`;
- `kernel/src/device/id.rs` SHA-256:
  `9da62c538cf9decb14dae949306ba5d73fb5ec5229109ffe9ddf7ee4742a40df`;
- `kernel/Cargo.toml` SHA-256:
  `6391c1b640b5b0aa565215a55f92947fcad63b2e913d63f490e4dd6f4561b0ec`;
- `kernel/Cargo.lock` SHA-256:
  `23154f5d592ba682018737ee09d890754eeac0fcda7cd2a07d729b410a31a61d`;
- `rust-toolchain.toml` SHA-256:
  `f25aa01d7f83c31506438cdbc0ab86bf5799db7fc1018dd477b5856ff86e9d01`;
- `kernel/.cargo/config.toml` SHA-256:
  `fce475e4de67895dbef63eb511d03b6840014340614f694b3627bf4dea45bfe2`;
  and
- `kernel/arch/x86_64/x86_64.json` SHA-256:
  `f8f9aab0ff28cb2c8c3a5aa7d544711278bf97dee9dcc24d1b9a0151e5e94539`.

The build identity is:

- `nightly-2025-05-10-x86_64-unknown-linux-gnu`;
- rustc commit `dcecb99176edf2eec51613730937d21cdd5c8f6e`, LLVM 20.1.4;
- Cargo commit `7918c7eb5`;
- custom target `kernel/arch/x86_64/x86_64.json`;
- release library target `kernel` from package `maestro`; and
- one codegen unit, linked-dead-code retention, LLVM textual emission, no
  incremental compilation, one Cargo job, and zero release debug info.

From each isolated `kernel/` directory the semantic build command is:

```text
cargo +nightly-2025-05-10 rustc --locked --offline --lib --release \
  --target arch/x86_64/x86_64.json --jobs 1 -- \
  -Ccodegen-units=1 -Clink-dead-code \
  --remap-path-prefix=<isolated-root>=/axeyum-external/maestro \
  --emit=llvm-ir
```

The runner sets distinct absolute `CARGO_TARGET_DIR` values, `CARGO_INCREMENTAL=0`,
`CARGO_BUILD_JOBS=1`, `CARGO_PROFILE_RELEASE_DEBUG=0`, and
`SOURCE_DATE_EPOCH=1783984251`. A non-credited online `cargo fetch --locked`
preparation may populate Cargo's checksum-validated cache; both credited builds
run offline. Each build runs in the standing 4 GiB memory cgroup and the source
root's normal `kernel/target/x86_64/release` directory is created because the
upstream build script expects that path even when `CARGO_TARGET_DIR` is
redirected.

The extraction identity is Ubuntu LLVM 21.1.8:

- `/usr/bin/llvm-extract-21` SHA-256
  `7c02041b5306536670c74f16c463f5026776f819f66a63effe11d88d352c069a`;
- `/usr/bin/llvm-as-21` SHA-256
  `50526d303ae33ed44002023d8d9611186e916f4b8eaf70a608bdbf1d81122784`.

The exact selected symbol set is:

```text
_ZN6kernel6device2id5major17h6277e663e5046b6eE
_ZN6kernel6device2id5minor17ha1a9fa0579be1b4dE
_ZN6kernel6device2id7makedev17h17016c0268a8943fE
```

Each symbol is extracted separately with `llvm-extract-21 --func=<symbol> -S`
and reassembled with `llvm-as-21`. Raw extracted hashes are diagnostic because
`llvm-extract` writes its input path into the first `; ModuleID =` line. The
canonical extracted hash excludes exactly that one matching line and no other
byte. The full rustc module permits no normalization and must be byte-identical
between roots.

## Frozen T5.5.2 gates

1. Commit this zero-result ADR before adding the capture tool, registration,
   result directory, parser tests, or any retained capture observation. The
   disposable feasibility module must not enter the repository or seed an
   expected output hash.
2. The input repository must contain the exact commit and tree, have the exact
   registered critical-file hashes, and report no tracked modifications.
   Branch names, current checkout, newer upstream commits, and an ordinary
   shallow-clone head never substitute for the registered object.
3. Materialize the registered tree into two distinct temporary absolute roots.
   Run the complete owning build from each root under the frozen environment.
   Exactly one final `kernel-*.ll` module exists per root, and the two complete
   modules are byte-identical in size and SHA-256. A root-dependent byte is a
   negative T5.5.2 result; do not add post-hoc full-module normalization.
4. Each complete module assembles under registered `llvm-as-21` and contains
   exactly one definition of each registered symbol. Missing, duplicate, or
   changed symbols fail before extraction. Other kernel definitions are
   expected in the full module and receive no semantic credit.
5. Extract all three symbols independently from both roots. Every raw output
   assembles. After only the frozen `ModuleID` exclusion, same-symbol canonical
   bytes and hashes match across roots. Cross-symbol canonical hashes must be
   distinct. Retain raw and canonical identity fields so normalization cannot
   hide any other drift.
6. Feed every extracted module to the existing non-panicking typed LLVM
   function parser and checked scalar reflector. Require exact parameter/result
   widths, one block, one return, no memory/call/loop, and explicit
   value+definedness terms. Canonical render/reparse preserves the typed graph
   and reassembles. This gate performs no solver query and claims no property.
   Any unsupported syntax is recorded as the result; it does not authorize a
   parser or source change.
7. Write one deterministic registration, one capture-result JSON document, and
   one human-readable report with complete tool/file/command identities, local
   artifact sizes and hashes, stage timings, peak RSS, stable outcome classes,
   and zero dropped targets. Run twice from the retained local artifacts and
   require byte-identical JSON after excluding explicitly labeled observation
   timing fields.
8. A later source-replay helper may mechanically extract the three exact
   function definitions from the authenticated local source into a temporary
   host harness. No copied body is committed. The T5.5.3 ADR must freeze this
   independent concrete replay before any countermodel is observed.
9. Mutation tests cover source, commit/tree, each critical hash, compiler,
   Cargo, target JSON, build argv, module count, every symbol, extraction tool,
   `ModuleID` grammar, non-`ModuleID` bytes, parser width/op/flag, existing
   output, and partial write. Each fails with a stable stage/kind and no
   credited artifact.
10. The committed path set contains no Maestro source, LLVM, bitcode, generated
    host harness, Cargo build product, or other compiler-derived target bytes.
    A repository path audit and staged-diff audit enforce this. Any future
    vendoring requires a separate recorded distribution/attribution decision.
11. Run scoped Python checks, synthetic capture-validator tests, the existing
    LLVM checked-scalar tests, reflection semantics gate, strict docs/link and
    whitespace checks, and the one-job 4 GiB kernel-journal OOM audit. No
    production IR/solver/reflection semantics, public API, dependency, feature,
    unsafe, MSRV, WASM, or scoreboard claim may change in T5.5.2.
12. T5.5.2 acceptance says only that the exact external build artifacts are
    reproducibly captured and admitted by the current parser. T5.5.3 requires
    a new zero-row ADR before constructing or solving the three inverse
    obligations, negative controls, source replay, or measured scoreboard row.

No gate may be weakened after the first official capture command starts. A
failure remains a committed negative result with its exact stage and stable
kind; it may select a separately preregistered prerequisite but cannot be
reclassified away.

## Result

Proposed. No official capture, extraction, parser-admission result, retained
external byte, proof, or scoreboard row exists under this ADR.

The first runner invocation was rejected before either credited build. It
placed the two disposable source roots below Axeyum's ignored `target/`
directory, so Cargo walked to Axeyum's ancestor workspace and rejected the
foreign Maestro manifest as an undeclared member. No module or parser result
was produced. The runner correction allocates only those two disposable source
roots from the system temporary directory; retained local outputs remain below
Axeyum's ignored `target/`. Source/tree validation, commands, toolchain,
two-root byte-identity, extraction, parser, local-only, and all other frozen
gates are unchanged.

## Rejected alternatives

- **Commit the feasibility LLVM module.** Rejected: it predates this protocol,
  was produced in one root, and crosses the unresolved artifact-distribution
  boundary.
- **Copy the three source functions into an Axeyum fixture.** Rejected: that
  would turn an external owning-build measurement into another curated input
  and would vendor upstream source.
- **Select Tock solely to avoid the distribution gate.** Rejected for this
  first cell: the audited useful Tock surfaces require enum ABI, slices/memory,
  or `ctlz`, while Maestro tests the already-supported scalar path. Tock remains
  a stronger later diversity target.
- **Extract first and authenticate only the small files.** Rejected: the claim
  is about functions emitted by Maestro's own build; the complete owning
  module must be reproduced before selection.
- **Normalize arbitrary root-dependent LLVM text.** Rejected: only the already
  understood extraction `ModuleID` field is excluded. Full-module drift is a
  result.
- **Widen the LLVM parser in response to the target.** Rejected: T5.5.2 measures
  the accepted fragment. Any genuine rejection needs its own preregistered
  semantic or syntax decision.

## Consequences

- A positive T5.5.2 result supplies an authenticated, reproducible, local-only
  external LLVM corpus and permits a separate T5.5.3 proof preregistration.
- A negative result precisely identifies acquisition, build reproducibility,
  extraction, or parser admission as the next prerequisite without moving the
  target or editing its source.
- The local-only boundary makes reproduction less convenient than committed
  fixtures, but avoids silently making a licensing decision and preserves the
  evidence chain through exact hashes and commands.

## References

- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [P5.5 Maestro selection](../../plan/track-5-verified-systems/P5.5-target-selection-maestro-device-id.md).
- ADR-0280 through ADR-0284 (typed LLVM scalar/CFG syntax and execution).
- ADR-0287 and ADR-0289 (authenticated compiler and owning-Cargo capture).
- ADR-0294 (ModuleID-agnostic extracted LLVM identity).
