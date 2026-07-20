# ADR-0289: Preregister Cargo-owned MIR target selection

Status: proposed
Date: 2026-07-20

Result state: zero-row; no target fixture crate, Cargo capture command, build
selector, generated MIR, or build-backed reflection test exists under this ADR

## Context

ADR-0287 binds one repository source file to exact raw `rustc -Zunpretty=mir`
bytes, and ADR-0288 selects and checks one named function from that authenticated
multi-function artifact. That closes the stale-fixture and first byte-memory
semantics risks, but it still does not satisfy T5.1.3's user-facing boundary: a
function in a target Cargo package cannot yet reflect from the MIR emitted by
that package's own build in one command.

Invoking `rustc` directly on a copied source is not equivalent to selecting a
Cargo package and target. Cargo owns crate name, edition, features, dependency
resolution, target kind, build configuration, and the final compiler invocation.
Conversely, accepting an implicit `cargo rustc` target would make a workspace's
default members or target inference part of the proof input. The selection must
therefore be explicit and recorded.

The MIR spelling remains unstable. This slice continues to require the exact
registered rustc 1.97.0-nightly identity from ADR-0287 and treats Cargo/compiler
stdout as untrusted input to ADR-0288's strict parser and checked reflector. It
does not adopt `rustc_private`, `stable_mir`, Charon, or a general Rust frontend.

## Decision

Add one `axeyum-verify` command named `axeyum-mir-build`. A single invocation
must require and record:

- a canonical `Cargo.toml` path;
- an exact package name;
- exactly one target selector, either `--lib` or `--bin NAME`;
- one exact MIR function name;
- the explicit target `usize` width, initially only the registered 64-bit
  profile;
- a rustc executable whose verbose identity exactly matches ADR-0287; and
- a caller-chosen, nonexisting raw-MIR output path plus an isolated Cargo target
  directory.

The command executes a code-owned `cargo rustc --locked` argument vector for
only that selected package/target. It sets the selected `RUSTC`, removes ambient
rustc wrappers, uses the deterministic capture environment from ADR-0287, and
captures stdout byte-for-byte while retaining stderr only as diagnostics. No
shell, `eval`, manifest-sourced command, output normalization, or implicit
package/target selection is permitted.

After Cargo succeeds, the command must decode stdout as UTF-8, select the named
function with `reflect::mir::syntax`, and run
`reflect_bounded_memory_checked` with the explicit target width. Only after all
three stages succeed may it atomically create the requested raw-MIR file. It
then prints one deterministic machine-readable summary containing the schema,
compiler and Cargo identities, canonical manifest/package/target/function
selection, the ordered Cargo and appended rustc arguments, raw byte count,
typed parameter/block/region/result shape, and canonical Axeyum terms for
result, panic, and final bytes. The output path is not part of the summary, so
two equivalent captures can compare byte-for-byte.

Every failure prints a stable top-level class and returns nonzero without a
reflection result or partial output. Existing output is never overwritten.
Syntax and reflection failures retain their stable inner class and source
location. Running Cargo may execute the selected target's build scripts; the
command is an explicit local build operation, not a sandbox for hostile crates.
That execution boundary must be documented in the help and frontend note.

Add one standalone, locked, dependency-free fixture package outside the Axeyum
workspace membership. Its library target owns a four-byte store-then-load
function with the same specification as ADR-0288. The fixture is evidence for
Cargo package/target ownership and must not replace or mutate ADR-0287's
authenticated direct-rustc fixture.

## Pre-implementation acceptance gates

The command, target fixture, captures, and semantic tests begin only after this
zero-row ADR is committed. The implementation must then satisfy all of the
following:

1. one documented command selects the standalone fixture's manifest, package,
   library target, function, 64-bit profile, rustc, target directory, and raw
   output without relying on the current directory or Cargo defaults;
2. two clean invocations produce byte-identical raw MIR and byte-identical
   summaries, and the summary's byte count equals the retained artifact;
3. the retained output is raw stdout from the selected target's own
   `cargo rustc --locked` build; the exact Cargo/rustc identities and complete
   code-owned argument selection are visible and deterministic;
4. the command passes the complete artifact through ADR-0288's named typed
   parser and checked reflector before writing output; a missing, duplicate,
   malformed, unsupported, or non-reflectable function cannot be reported as a
   successful capture;
5. the build-backed store/load reflection proves the same guarded result,
   exact `index >= 4` panic predicate, selected-byte update, and preservation of
   other bytes as the authenticated direct-rustc and accepted LLVM fixtures;
6. sampled in-bounds executions and one solver-produced out-of-bounds witness
   replay against the ordinary fixture crate function; every value or final-
   memory claim is guarded by `!panic`;
7. missing/escaping manifests, wrong package/target/function, conflicting
   target selectors, non-64-bit configuration, wrong compiler identity, Cargo
   failure, non-UTF-8 output, checked syntax/reflection failure, existing output,
   and output-write failure have stable distinct top-level classes;
8. every failure before commit leaves the requested output absent, and an
   existing output remains byte-identical; temporary files stay under the
   caller-selected target/output parents and are removed on failure;
9. deterministic malformed arguments and target MIR never panic the command,
   and parser/reflection details preserve precise located errors rather than
   coercing or skipping unsupported input;
10. ambient `RUSTC_WRAPPER`/`RUSTC_WORKSPACE_WRAPPER`, workspace default members,
    and current-directory changes cannot alter the selected compiler, package,
    target, function, or result;
11. ADR-0287's source, raw output, provenance, and checksums remain byte-
    identical; no new third-party dependency, workspace member, default feature,
    native dependency, `rustc_private`, MSRV, or WASM surface is added; and
12. focused command/selection/failure/replay tests, the complete
    `axeyum-verify --all-features` suite, workspace formatting, strict Clippy and
    rustdoc, ADR-0287 exact fixture replay, and repository links pass.

The gates may be strengthened before the target fixture or first command code
is added. They may not be weakened after a Cargo capture or semantic result is
observed.

## Consequences

If accepted, T5.1.3 gains its first honest one-command target-package path:
Cargo selects and compiles the function's owning target, while Axeyum strictly
checks the emitted artifact before retaining or describing a reflection. The
same command and summary can later support compiler/build reproducibility
studies without treating compiler output as trusted.

This does not complete arbitrary target-crate support. The admitted semantics
remain ADR-0288's bounded acyclic scalar/one-byte-array profile; features,
cross-compilation, dependencies, build scripts, multiple codegen units, generic
monomorphizations, modules with ambiguous MIR names, general places, calls,
loops, drops, unwinds, and `stable_mir` remain separately gated. It also does
not harden Glaurung LLIR or admit a binary-vs-IR differential.

## Alternatives

- Keep using the direct-rustc fixture: rejected because it cannot prove Cargo
  package/target selection or the target crate's own build boundary.
- Run an implicit `cargo rustc` in the caller's current directory: rejected
  because workspace defaults and target inference would become hidden proof
  inputs.
- Capture first and validate later: rejected because malformed or unsupported
  MIR could be retained and mistaken for a checked frontend result.
- Add `stable_mir` or a compiler driver now: deferred because it changes the
  dependency/trust boundary and is not required to close this build-selection
  seam.
- Start general MIR places first: deferred because widening semantics while no
  real Cargo target can reach the checked path would optimize the wrong
  boundary.

## References

- ADR-0287 and ADR-0288.
- T5.1.3 and T5.1.5 in the Track 5 reflection plan.
- `docs/consumer-track/verify/real-rust-frontend.md`.
