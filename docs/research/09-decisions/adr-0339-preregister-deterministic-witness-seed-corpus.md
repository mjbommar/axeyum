# ADR-0339: Preregister deterministic replay-checked witness seed corpora

Status: accepted
Date: 2026-07-21

## Context

P5.4/T5.4.1 already turns reflected terms into deterministic differential-fuzz
oracles. T5.4.2 is the other direction of the same loop: a solver
countermodel should become a durable fuzz seed and a runnable regression test,
not disappear into a log or remain hand-copied in one test module.

The required pieces exist but are not composed. `Verdict::Counterexample`
carries typed source inputs; raw reflection proofs carry replayed models; and
`axeyum-property::render_reproduction_test` plus
`axeyum_verify::reproduce::render_counterexample_test` emit deterministic Rust
test source. There is no versioned corpus, no fail-closed admission API, and no
single fixture proving that solver output reaches a committed test unchanged.

This is correctness infrastructure, not a solver-performance mechanism. It
implements the Glaurung reviewer lesson that precise failures and replayable
evidence are Axeyum's lead contribution. It cannot revive the superseded warm-
speed headline, reopen concretization coverage, or authorize symbolic memory.

The preimplementation audit also finds one renderer defect that must be fixed
before a corpus can claim exact typed replay. `signed_value` treats widths above
127 as unsigned low bits. For width 128 it therefore renders the bit pattern
`0x8000...0000` as zero instead of `i128::MIN`; the same helper feeds scalar,
array, and macro-generated replays. Rust `i128` represents that value exactly.
No corpus result is admitted on top of this known boundary.

## Decision

Add one public `axeyum_verify::witness_corpus` module that accepts only
replay-confirmed counterexamples and deterministically renders a versioned seed
corpus plus Rust regression tests through the existing reproduction layer.

The v1 boundary is:

1. `WitnessSeed::from_verdict` accepts only `Verdict::Counterexample` and clones
   its exact class and declaration-ordered inputs. `Verified` and `Unknown`
   return distinct typed errors; neither can be relabeled as fuzz evidence.
2. `WitnessSeed::from_counterexample` admits replayed raw/reflection
   countermodels after the caller has lifted them to the existing `Witness`
   type. It does not add another model or value representation.
3. Both constructors require a caller-supplied replay callback and invoke it
   exactly once before returning. `false` is a typed `ReplayFailed` error and
   produces no seed. The callback is where the owning source/reflection test
   checks the original semantics; the corpus never infers replay from a solver
   verdict.
4. A replay recipe is either a constrained panic call (Rust path plus arguments
   that are exactly `name` or `&name` references to carried inputs) or an
   explicit caller-owned Rust assertion body for normally returning contract
   violations and equivalence refutations. Model/class strings never become
   executable source. Both recipes delegate final formatting to the existing
   reproduction renderers.
5. `WitnessSeedCorpus` owns a nonempty stable suite ID and unique stable seed
   IDs. It stores seeds in lexical ID order regardless of insertion order,
   rejects duplicates, and emits two deterministic byte streams: concatenated
   Rust tests and canonical compact JSON with schema
   `axeyum.verify.witness-seed-corpus.v1`.
6. The JSON carries suite, seed ID, class, replay kind, `replay_checked=true`,
   declaration-ordered input name/Rust type/Rust literal, and exact generated
   test source. Integer literals remain strings so 128-bit values do not pass
   through lossy JSON-number consumers. JSON escaping covers every control
   character.
7. V1 accepts `Bool` and native Rust integer widths 8/16/32/64/128, including
   fixed arrays of those integer types. Invalid names, non-native widths,
   malformed constrained call arguments, width/value drift, and unsupported
   witness shapes fail with precise typed errors. Existing source-produced
   witnesses remain unchanged.
8. Correct `signed_value` for width 128 before corpus admission. Width 128 uses
   exact two's-complement reinterpretation; widths 1--127 retain masked
   subtraction; width 0 or above 128 remains fail-safe and is rejected by the
   corpus API. Do not introduce coercion or truncate a carried value.
9. The library returns bytes only. It performs no filesystem writes, git
   mutation, process execution, or hidden source compilation. Callers own
   atomic file placement and review; a committed exact fixture demonstrates
   the intended workflow.

No new IR term, sort, solver route, model policy, native dependency, unsafe
code, or evidence trust step is added. T5.4.3's `Unknown` handoff and T5.4.4's
proof-versus-fuzz coverage report remain separate increments.

## Frozen evidence gates

Implementation is accepted only if one committed bundle passes all of these
gates:

1. Commit and push this zero-result ADR and PLAN/STATUS registration before
   adding production corpus code or observing generated fixture bytes.
2. Unit tests cover exact scalar and array literal rendering at signed/unsigned
   min, max, zero, and all-ones boundaries for widths 8/16/32/64/128. Dedicated
   width-128 checks require `i128::MIN`, `i128::MAX`, `-1i128`, and their array
   forms to round-trip; deterministic sampled widths 1--127 retain the existing
   mathematical interpretation.
3. Three independently obtained countermodels enter one corpus:
   a panic/overflow `Verdict::Counterexample`, a normally returning source-
   contract postcondition violation, and a raw QF_BV equivalence refutation.
   Each replay callback checks the original function or both compared
   computations before the seed is created.
4. The generated panic test uses `render_counterexample_test`; custom contract
   and equivalence bodies use `Reproduction`/`render_reproduction_test`. The
   exact concatenated generated source is committed, included by an integration
   test, compiled, and executed as ordinary Rust tests.
5. The exact canonical JSON is committed beside the generated source. A clean
   solver-to-corpus regeneration matches both files byte-for-byte. Reversing
   insertion order leaves both outputs unchanged.
6. Negative tests reject `Verified`, `Unknown`, a false replay callback,
   duplicate seed IDs, empty/invalid suite or seed IDs, invalid input names,
   unsupported widths, malformed call paths/arguments, and JSON control-string
   injection. Every error variant and display message names the failing field
   and observed value; no failure becomes an empty corpus or bare `Unknown`.
7. A witness/class mutation changes the exact artifact and makes the committed-
   fixture comparison fail. A replay mutation fails before rendering. No seed
   can claim `replay_checked=true` through an unchecked constructor or public
   mutable field.
8. Existing macro-generated reproduction tests, `reproduce_render`, source-
   contract replay, reflection countermodels, and the 123-test semantics gate
   remain green. The public API is documented with one compile-checked example
   and stable ordering/error contracts.
9. Formatting, strict all-target/all-feature Clippy, warning-denied rustdoc,
   the complete `axeyum-verify` package, the reflection semantics gate, and docs
   links pass with one Cargo job inside the 4 GiB cgroup and test debug info
   disabled. A capped OOM is a failed gate.
10. Update P5.4, PLAN, STATUS, the research question, and the ADR index with the
    accepted exact counts and artifact identities; commit and push without
    staging unrelated benchmark/corpus/review files.

No performance, bug-discovery-rate, coverage, general-Rust, whole-program, or
automatic-git claim follows from this cell. "Automatically" means one checked
API path from a solver result to deterministic reviewable bytes; committing the
bytes remains an explicit user action.

## Rejected alternatives

- **Write tests directly from the library.** Rejected: hidden filesystem and git
  side effects are inappropriate for a verification library and make review and
  atomicity harder.
- **Serialize `Model` directly.** Rejected: it would bypass typed source lifting,
  leak arena-local symbol identity, and fail to describe executable Rust inputs.
- **Accept any verdict with a string status.** Rejected: `Unknown` is first-class
  and must never become a seed or proof by relabeling.
- **Trust `Counterexample` without source replay.** Rejected: the entire
  consumer soundness floor is that a model becomes evidence only after replay.
- **Add `serde` to every public witness type.** Rejected for v1: a narrow
  canonical renderer keeps the artifact schema explicit without changing the
  existing API or default dependency envelope.
- **Combine directed-fuzz handoff and coverage accounting.** Deferred to
  T5.4.3/4 so decided witnesses cannot be conflated with fuzz-only samples.

## Consequences

- A replayed solver witness becomes a stable, source-reviewable artifact and a
  compiled regression test through one bounded API.
- Exact errors and 128-bit value fidelity become regression-owned rather than
  implicit assumptions.
- The corpus schema creates the input side of the later proved/refuted/fuzzed-
  only report without prematurely claiming that report or its coverage.

## Result

Accepted. The prerequisite fix at `873c671e` gives exact two's-complement
interpretation for every width 1--128, including width-127 negative boundaries
and `i128::MIN`. Six renderer tests now cover sampled full-width interpretation,
exact signed/unsigned native-width scalar and array boundaries, and compiled
`i128::MIN`/`i128::MAX` literals.

Production commit `75971d1d` adds the public fail-closed
`witness_corpus` module. `WitnessSeed` has no unchecked constructor or public
mutable fields: a typed replay callback must succeed before a seed exists;
`Verified`, `Unknown`, malformed fields/witnesses, false replay, duplicates,
and empty corpora remain typed errors. The module returns deterministic bytes
and performs no filesystem, process, or git operation.

Fixture commit `1efa7f25` carries three independently obtained and replayed
countermodels in one lexical corpus:

- macro overflow: `x=255u8`, replayed as an actual `corpus_overflow` panic;
- source postcondition: `x=0u8`, replayed as a normal return that violates the
  original postcondition;
- raw QF_BV equivalence: `x=0u8`, replayed in the source term arena and against
  both real Rust functions.

The canonical JSON is 1,404 bytes with SHA-256
`fa44878a0cde494a18883f6635dab1047a210469289c1cb058a02a4624246575`.
The exact generated Rust source is 712 bytes / 27 lines with SHA-256
`7e161d411c54c97eaa314f2c1a0e8e68558eb1b18cda8fee2268d5dccea20bef`.
It is committed, included, compiled, and executed. Reverse insertion reproduces
both files byte-for-byte; a replay-valid witness mutation changes both, while a
false replay fails before rendering.

The focused corpus integration has six passing tests (two macro verdict gates,
three exact generated regressions, one canonical/ordering/mutation gate), and
the corpus module has four fail-closed unit tests. The complete
`axeyum-verify --all-features` package and doctests pass; strict all-target,
all-feature Clippy and warning-denied rustdoc pass. The current reflection
semantics gate passes 129 tests across 12 binaries plus its ten checker tests,
with 82 registered variants, 34 proof tests, 18 refutation tests, and 26 fuzz
tests. Every Cargo command ran with one job inside the 4 GiB cgroup; no capped
OOM occurred.

This closes T5.4.2 only. It does not claim a bug-discovery rate, proof/fuzz
coverage, general Rust support, or performance leadership. T5.4.3's honest
`Unknown` handoff is the next phase cell and requires a separate zero-result
ADR before implementation; T5.4.4 remains separate.

## References

- [P5.4 fuzz-oracle loop](../../plan/track-5-verified-systems/P5.4-fuzz-oracle.md).
- [Glaurung feedback reconciliation](../08-planning/glaurung-feedback-reconciliation-2026-07-20.md).
- [ADR-0056 verified-systems track](adr-0056-verified-systems-track.md).
