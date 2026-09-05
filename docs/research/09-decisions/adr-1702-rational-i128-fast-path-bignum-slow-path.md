# ADR-1702: Exact rationals are an `i128` fast path with an arbitrary-precision slow path

Index-summary: `Rational` promotes to arbitrary precision on `i128` overflow instead of declining (slice 1: `Rational`; slice 2: `Value::Int` and the parser)
Index-status: accepted
Status: accepted
Date: 2026-09-05

## Context

[`crates/axeyum-ir/src/rational.rs`](../../../crates/axeyum-ir/src/rational.rs)
has been `struct Rational { num: i128, den: i128 }` since ADR-0015. Exactness
was never in question; *range* was. The bounded-arithmetic stance of
ADR-0014/0015 made `i128` overflow a **usage error**: `Rational::new` panicked,
the `checked_*` family returned `None`, and
[`simplex.rs`](../../../crates/axeyum-solver/src/simplex.rs) mapped that `None`
to `SimplexOutcome::Unknown`. Sound, and lossy.

Four consequences are on the record:

- The 2026-09-05 performance and architecture review, §3.2 **D4**, names the
  two-`i128` representation as a first-order architectural constraint.
- [`docs/plan/gap-analysis-smt-solvers-2026-08-21.md`](../../plan/gap-analysis-smt-solvers-2026-08-21.md)
  §9 row **4b**: 26 of the 200 QF_UFLIA competition files carry integer
  literals above `2^127` (78-digit EVM `2^256` words). Axeyum decides **0 of
  26** — they are rejected before any solver work. cvc5, the parity reference,
  decides 6; z3 decides 12.
- [`docs/plan/status/111-nra-handelman-cert.md`](../../plan/status/111-nra-handelman-cert.md)
  records a Handelman certificate whose exact derivation needs a numerator
  around `1.6·10^57`, which does not fit an `i128` product, so the lane carried
  a relaxation instead of the exact coefficient.
- The online CDCL(T) LRA route's 1,024-atom cap is *partly* an overflow guard
  rather than a memory bound: 71 of the QF_LRA files in the 2026-08-21
  diagnosis decline on it.

`num-bigint`, `num-rational`, `num-integer` and `num-traits` are **already**
unconditional dependencies of `axeyum-ir` (ADR-0045, for `RealAlgebraic` and
`poly_big.rs`). They are pure Rust, so nothing here touches the no-C/C++ hard
rule. [`wide.rs`](../../../crates/axeyum-ir/src/wide.rs)'s `WideUint` is the
in-tree precedent for the same shape in the bit-vector direction.

## Decision

**Exact rational arithmetic in the IR is an `i128` fast path with an
arbitrary-precision slow path: `i128` overflow PROMOTES the value to
`num_rational::BigRational` instead of declining, and a result that fits `i128`
again DEMOTES back to the fast path.**

Detail:

- The public API of `Rational` does not change shape. Every existing `pub fn`
  keeps its name and signature, so the 223 files and ~5,500 references that
  consume the type compile unchanged.
- `Rational` stays `Copy`. This is a hard constraint, not a preference: it is
  consumed by value in ~5,500 places and is a field of the interned
  `TermNode::RealConst`. `BigRational` is heap-owned and therefore not `Copy`,
  so the big representation is a **handle** into a process-global,
  deduplicating, append-only pool, encoded in the existing 32 bytes by the
  otherwise-impossible `den == 0` (the small invariant is `den > 0`). The
  struct's size and layout are unchanged, so the dense simplex tableau's
  memory model is unchanged.
- The pool is capped (`Rational::big_pool_capacity()`). Past the cap,
  promotion fails and every operation behaves **exactly as it does today** —
  `checked_*` returns `None`, the operators panic. The cap is what keeps an
  append-only pool from turning today's fast `unknown` into an OOM.
- Functions that returned `None` on overflow keep their signatures and now
  return `Some` on the promoted path; each such function documents that.
  `Rational::new` no longer panics on overflow (`den == 0` is still a usage
  error and still asserts). `checked_cmp` now always returns `Some`, because
  comparison never allocates a pool entry.
- `Ord`, `Eq` and `Hash` are **value-based and representation-independent**: a
  value that fits `i128` hashes and compares identically whether it was built
  small or arrived by demotion from big. Because promotion only ever happens
  for values that do *not* fit `i128`, and because every result that fits is
  demoted, each rational value has exactly one representation — the
  canonicality that `TermNode` interning depends on is preserved.

### Two slices

| slice | scope | lane |
|---|---|---|
| 1 | `Rational` itself, plus the `simplex.rs` overflow marker | this ADR's lane (landed) |
| 2 | `Value::Int(i128)` in [`value.rs`](../../../crates/axeyum-ir/src/value.rs) and the SMT-LIB integer-literal parser | a later lane; **not started** |

Slice 1 does not admit a single one of the 26 QF_UFLIA files. Those are
rejected at the *parser*, on `Value::Int(i128)`, before any `Rational` exists —
slice 2 is what admits them. Slice 1 is the foundation and the smaller,
independently testable half: it removes overflow as a source of `unknown` in
the LRA/LIA/NRA arithmetic that is already reached.

## Determinism and soundness argument

The two paths compute **the same mathematical value**. `BigRational::new`
normalizes to lowest terms with a positive denominator, which is the same
canonical form the `i128` path maintains, and the demotion check is exact
(`BigInt::to_i128`). So:

- **No verdict can change from one to the other.** A `sat` remains `sat` with
  the same model (the witness is the same rational number, possibly now
  representable); an `unsat` remains `unsat` with the same Farkas multipliers.
  The only reachable transition is `Unknown → sat` or `Unknown → unsat`, on
  queries where the arithmetic previously ran out of range. No previously
  decided query can be re-decided differently, because on every input where
  the old code produced a value, the new code produces the identical value by
  the identical `i128` operations.
- **Determinism is preserved.** The pool id is never observable: `Eq`, `Ord`,
  `Hash` and `Display` are all defined on the value, not the handle. Two runs
  that interleave differently can assign different ids to the same value and
  still produce byte-identical output, and a `HashMap` keyed by `Rational`
  iterates in the same order in both.
- **Replay is unaffected.** A `sat` model is still checked by evaluating the
  original term against the lifted model; the evaluator's arithmetic is the
  same `Rational`, now with a wider range.

### The residual hazard, named

`numerator()` and `denominator()` return `i128` and are called at 416 sites.
They keep that signature, and they **panic with a clear message** on a value
outside `i128`. Saturating or truncating was rejected outright: it converts an
out-of-range value into a silently wrong one, which is the one failure mode
this project does not accept. New accessors give callers a non-panicking
route — `checked_numerator()`, `checked_denominator()` (both `Option<i128>`)
and `numerator_big()` / `denominator_big()` (`BigInt`) — plus `is_big()`.

This is a real change in exposure: before, a big rational could not exist, so
no caller could meet one. It is a *loud* change, not a silent one, and it is
bounded by the routes that actually produce big values. Auditing those 416
sites route by route is slice 2's work, alongside `Value::Int`. Any route that
must not panic uses `checked_numerator()`.

## Evidence

- Fast-path cost: the promotion test is `den > 0` on each operand — two
  compares on a value already in a register, ahead of arithmetic that is
  unchanged instruction for instruction. Measured against the
  `simplex_incremental_check_feasible_lp` and `arena_intern` criterion
  benchmarks before and after, pinned to `taskset -c 0-7`; the deltas are in
  the lane status file. A regression beyond the measured noise band was a
  blocking condition for landing.
- Property test: every operation (`+`, `-`, `*`, `/`, `neg`, `recip`, `cmp`)
  compared against `BigRational` computed directly, over a seeded generator
  that deliberately straddles `2^127`.
- Discriminating evaluation tests: products around `2^127`; the exact
  `1.6·10^57` Handelman numerator; a chain that grows past `i128` and cancels
  back into range (verifying demotion, so the fast path is retaken after
  transient growth); representation-independent `Eq`/`Ord`/`Hash`.

## Alternatives

- **Drop `Copy`, box the big case.** The textbook representation, and the one
  this ADR would choose in a new codebase. Rejected on measurement: `Rational`
  is referenced ~5,500 times in 223 files, consumed by value throughout, so
  the change is a workspace-wide mechanical edit that would conflict with
  every concurrent lane. Revisit only behind a dedicated refactor with the
  tree quiet.
- **Widen to a fixed `i256`/`i512` inline.** Keeps `Copy` and needs no pool,
  but quadruples the size of a tableau cell (the dense simplex budget is
  written in cells), and still has a ceiling — it moves the wall rather than
  removing it.
- **Leak each big value with `Box::leak` instead of pooling.** Simpler, but
  loses deduplication, so memory grows with the number of *operations* rather
  than the number of distinct values, and equality becomes a value comparison
  in every case.
- **Keep declining, and raise the LRA atom cap instead.** Does not address
  row 4b at all, and the cap is a memory bound as well as an overflow guard —
  raising it is a separate lever, measured separately.

## Consequences

- `simplex.rs`'s `Overflow` marker stays. It is **not** unreachable after
  slice 1: `checked_div` still returns `None` on division by zero, and
  promotion still fails at the pool cap. Removing it would delete a live
  soundness path. The pivot and deadline budgets are untouched, so the
  simplex's termination and determinism arguments are unchanged.
- The LRA atom cap does **not** move in slice 1, and slice 1 does not claim
  it. Turning that cap from a partial overflow guard into a pure memory bound
  is a follow-up that must be measured on its own.
- `axeyum-ir` gains a process-global mutable pool. It is the first one in the
  crate. It is documented as append-only and capped, and `big_pool_len()` is
  exposed so a test or a diagnosis can see it.
- Slice 2 (`Value::Int`, the parser, and the 416 accessor sites) is now
  unblocked and is the change that admits the 26 QF_UFLIA files.
