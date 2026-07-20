# ADR-0290: Preregister the reflection semantics coverage gate

Status: proposed
Date: 2026-07-20

Result state: zero-row; no semantics manifest, manifest checker, dedicated gate
test, or dedicated CI job exists under this ADR

## Context

T5.1.6 requires every newly admitted reflection operation or instruction to
land with both a symbolic equivalence/specification proof and deterministic
fuzz coverage, with `DISAGREE = 0` as a standing CI condition. The repository
already has strong pieces: 16 positive cross-IR tests, five replay-checked
wrong-transform refutations, checked scalar/CFG/memory proofs, parser-noise
tests, and the reusable `DiffFuzz` harness. Ordinary workspace CI executes
those tests, but nothing currently proves that the evidence set remains
complete when the checked frontend's semantic enums grow.

The current cross-IR fuzz also trails the proof fixtures. It covers six
MIR/LLVM pairs (`masked`, both `sel` forms, `sar`, `scale`, and one `lut` form)
but omits the accepted LLVM-switch `lut` form, `ext`, `notx`, `negate`, and the
two-input `umin` pair. The hypothesis-bounded `lut3`/`unreachable` case has a
proof but no corresponding defined-domain differential run. A green workspace
test therefore does not yet establish the T5.1.6 standing claim.

The checked semantic surface is finite and explicit today. Across LLVM
`BinaryOpcode`, `IntPredicate`, `CastOpcode`, `Intrinsic`, `SemanticFlag`,
`GepFlag`, `ScalarInstructionKind`, and `TerminatorKind`, and MIR
`BinaryOpcode`, `Rvalue`, `StatementKind`, and `TerminatorKind`, there are 62
variants. This ADR gates that source-owned surface. It does not count error,
operand, type, or storage-representation enums as semantic operations.

This work directly serves the reviewer feedback: strict translation and precise
failures remain the lead contribution, so semantic coverage must be visible and
fail closed rather than inferred from a large undifferentiated suite. It adds no
coercion, fallback interpretation, solver-performance claim, or Glaurung LLIR
admission.

## Decision

Add a versioned machine-readable manifest at
`docs/consumer-track/verify/reflection-semantics-gate.json`. It names the exact
Rust source file and enum for each of the 12 semantic surfaces and groups every
derived `Enum::Variant` key under evidence that contains:

- at least one symbolic equivalence or independently constructed specification
  test;
- at least one deterministic differential, source-replay, or semantic-fuzz
  test; and
- optional negative/refutation evidence where a discriminating control exists.

Add `scripts/check-reflection-semantics-gate.py`. The checker must parse the
named enum declarations from the repository source, derive the 62 current keys,
and require exact one-to-one coverage by manifest evidence groups. It rejects a
missing, duplicate, orphaned, or misspelled variant; absent test file or test
function; duplicate evidence-group ID; missing proof/fuzz side; unexpected
schema; escaping path; or drift in the dedicated command/test-binary list. The
checker validates test declarations, not prose mentions.

The enum parser is deliberately narrow: it accepts the ordinary named variants
used by these source enums while balancing nested tuple/struct payloads. It is
not a general Rust parser. Its own unit tests must mutate temporary source and
manifest copies to prove that a new source variant, a removed evidence member,
a duplicate member, and a nonexistent test function all fail closed.

Add a dedicated Rust semantics matrix for the checked scalar LLVM fragment.
Every current binary opcode, integer predicate, cast, intrinsic, and semantic
flag must have an all-input symbolic specification at a bounded width plus a
deterministic host-oracle differential run. Undefined/poison-producing cases
compare both value (only when defined) and definedness; the test must not
mistake SMT-LIB-total BV division or shifts for LLVM-defined execution.

Complete the cross-IR differential table so all 11 ordinary accepted MIR/LLVM
pairs run through `DiffFuzz`, including the two-input `umin` case. Add a bounded
defined-domain differential control for `lut3`; values outside its explicit
hypothesis remain undefined rather than being compared to a fabricated result.
The five wrong-transform cases remain mandatory replay-checked negative
controls.

For CFG, bounded byte-memory, and checked MIR families, the manifest may cite
the existing exact proof and deterministic fuzz/source-replay tests, but every
one of the 62 source variants must be owned by exactly one evidence group. A
new operation cannot become a checked public semantic variant until the source
enum, manifest ownership, proof/spec test, and fuzz/replay test land together.

Wire a `reflection-semantics-gate` recipe into `just check` and a dedicated
stable CI job. The job runs the manifest checker and only the named bounded
test binaries, including the scalar matrix, cross-IR equivalence/refutation,
checked LLVM CFG/memory, and checked MIR memory suites. Ordinary workspace CI
remains defense in depth; the dedicated job makes the standing contract visible
and independently runnable.

## Pre-implementation acceptance gates

The manifest, checker, scalar matrix, cross-IR expansion, and CI/`just` wiring
begin only after this zero-row ADR is committed. The implementation must then
satisfy all of the following:

1. the checker derives exactly 62 semantic keys from the 12 registered source
   enums, and the manifest owns every derived key exactly once with no extras;
2. each evidence group names at least one existing `#[test]` for symbolic
   proof/specification and one existing `#[test]` for deterministic
   fuzz/differential/source replay; prose, helper functions, and ignored tests
   do not satisfy the gate;
3. all 13 LLVM binary opcodes, 10 predicates, three casts, two intrinsics, and
   five semantic flags receive bounded all-input specification proofs and
   deterministic host-oracle comparison of value plus definedness;
4. every undefined or poison-producing scalar case is guarded explicitly;
   division by zero, signed minimum divided by minus one, oversized shifts,
   `exact`, wrap, disjointness, truncation, and `nneg` controls cannot pass via
   total BV placeholder values;
5. all 11 ordinary MIR/LLVM pairs run deterministic `DiffFuzz` with explicit
   widths/seed/sample counts, including the two-input `umin` pair, and report
   `DISAGREE = 0`;
6. the `lut3` pair fuzzes only its registered `x < 3` defined domain while its
   existing proof continues to refute unconditional LLVM definedness;
7. all five wrong-transform cases still return replay-checked countermodels;
8. LLVM CFG, LLVM bounded-memory, and MIR bounded-memory semantic families map
   to existing exact proof plus deterministic noise/source-replay evidence,
   without weakening strict unsupported-construct errors;
9. checker unit tests prove fail-closed behavior for source-variant drift,
   missing/duplicate/orphan evidence, missing proof/fuzz sides, bad test names,
   path escape, and command-list drift;
10. one documented local command and one dedicated stable CI job run the exact
    same checker and bounded test-binary set; a future enum variant fails that
    job until its two evidence sides are registered;
11. the manifest and checker outputs are deterministic and add no third-party
    dependency, feature, native library, unsafe code, MSRV change, or WASM
    surface; and
12. the focused gate, complete `axeyum-verify --all-features` suite, workspace
    formatting, strict Clippy and warning-denied rustdoc, exact MIR fixture
    replay, and repository link checks pass.

The gates may be strengthened before the first manifest observation. They may
not be weakened after the source inventory or coverage result is observed.

## Consequences

If accepted, T5.1.6 becomes an executable admission contract rather than a
convention. The frontend can still grow, but every semantic variant makes its
proof and concrete oracle obligations visible in the same change. Reviewers can
inspect a small deterministic gate instead of inferring coverage from test
volume.

This does not prove arbitrary compiler correctness, replace source replay, or
make the admitted LLVM/MIR fragments complete. It does not authorize loops,
general MIR places, wide/aliased memory, `stable_mir`, LLIR lowering, or a shared
frontend crate. Those remain separately gated.
