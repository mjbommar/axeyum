# ADR-0326: Preregister stable-virtual-root Maestro capture

Status: proposed
Date: 2026-07-21

## Context

ADR-0323 rejects final-crate-only path remapping. ADR-0324 finds seven
unremapped dependency paths and broad identity drift. ADR-0325 applies the
remap dependency-wide and eliminates every real-root token, but its two raw
modules still differ: each build passes a different remap-rule source string
into rustc/Cargo identity.

The next route must make every visible path and flag byte identical while
retaining genuinely separate physical source and target roots. This host has a
working unprivileged Bubblewrap 0.11.1, so each build can run sequentially in a
fresh mount namespace with its physical inputs bound at the same virtual paths.
No output normalization or root-specific compiler flag is needed.

## Decision

Create a v3 capture producer. Materialize two separate source trees and two
separate Cargo target directories, then run each build under registered
`/usr/bin/bwrap` with:

- its physical source root bind-mounted read/write at
  `/axeyum-vroot/source`;
- its physical Cargo target directory bind-mounted read/write at
  `/axeyum-vroot/target`;
- build cwd `/axeyum-vroot/source/kernel`;
- `CARGO_TARGET_DIR=/axeyum-vroot/target`; and
- no `RUSTFLAGS`, `CARGO_BUILD_RUSTFLAGS`, `CARGO_ENCODED_RUSTFLAGS`, path-remap
  rustc tail, or post-build normalization.

The upstream `.cargo/config.toml` supplies its original
`-Zexport-executable-symbols`; the final rustc tail remains only one codegen
unit, linked-dead-code retention, and textual LLVM emission.

## Frozen v3 gates

1. Commit this zero-result ADR before adding/running v3. Prior module hashes do
   not seed a v3 expected hash.
2. Reuse ADR-0323's exact source/toolchain/target/build/resource/local-only
   identities and ADR-0325's final rustc tail. Reject all ambient Rust flags.
3. Register `/usr/bin/bwrap` at SHA-256
   `0abea81db798ebf6b4742ac0664802d97521547a353c2a0dbdc21d76cbbfd2c0`
   and version `bubblewrap 0.11.1`. Before builds, run a no-write probe with
   `--die-with-parent --new-session --unshare-all --ro-bind / / --dev-bind
   /dev /dev --proc /proc`; failure is the result.
4. The namespace argv and mount order are identical across runs except the two
   host-side bind sources. Both in-namespace destinations, cwd, Cargo target,
   build command, environment, and ordered flags are byte-identical.
5. Keep separate physical source and target roots. Precreate the upstream-
   expected `kernel/target/x86_64/release` directory in each source tree. Run
   each build offline, one job, inside the standing 4 GiB scope.
6. Require one assembling `kernel-*.ll` per target. Each module contains zero
   physical source/target/temp-parent tokens. Record occurrences of the fixed
   virtual source and target paths; corresponding counts must match.
7. Require raw full-module size and SHA-256 equality without normalization.
   Any mismatch stops before extraction and closes v3 negatively.
8. Only after equality, discover exactly one selected definition per demangled
   comment/constrained mangled shape, require identical symbols, extract and
   assemble all three, require ModuleID-agnostic and frontend-canonical
   equality, and pass exact scalar admission widths/profile.
9. Commit only Axeyum-owned code, registration, metadata hashes/counts, and
   result prose. All source/modules/extractions/build products remain ignored
   local bytes; the licensing boundary is unchanged.
10. Mutation tests cover bwrap hash/version/argv/mount destination/order,
    physical-root aliasing, ambient flags, virtual path/env drift, root-token
    leakage, module inequality, symbol/extraction/parser failures, and atomic
    output. Stable stage/kind and zero partial credit are mandatory.
11. Run focused producer/admission/LLVM semantics tests, strict docs/links,
    result recomputation, and OOM audit. No production semantics/API/dependency/
    feature or solver/scoreboard claim changes.
12. Success closes local-only reproducible T5.5.2 capture/parser admission and
    permits a separate zero-row T5.5.3 ADR. It authorizes no property query,
    source replay, negative control, proof, or measured claim.

No gate may be weakened after the first v3 build starts. Failure ends the
Maestro build-route correction rather than licensing v4 normalization.

## Result

Proposed. No virtual-root build, module, extraction, parser result, capture
credit, proof, or scoreboard row exists.

## Rejected alternatives

- **More remap flags.** Rejected: v2 shows root-specific rule inputs remain an
  identity variable after emitted path text is fixed.
- **One physical tree twice.** Rejected: it does not test independent capture.
- **Symlink-only virtual roots.** Rejected: tool canonicalization may recover
  physical paths; mount namespaces give each process the same visible path.
- **Normalize v2 output.** Rejected: raw owning-build equality remains the gate.

## Consequences

- v3 isolates path identity at process input rather than rewriting output.
- Success yields the first authenticated external local corpus; failure ends
  this route honestly while preserving all prior negative evidence.

## References

- ADR-0323 through ADR-0325.
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
