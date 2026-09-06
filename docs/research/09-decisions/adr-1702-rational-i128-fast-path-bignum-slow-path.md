# ADR-1702: Exact rationals are an `i128` fast path with an arbitrary-precision slow path

Index-summary: `Rational` gets an opt-in `wide_*` family that promotes to arbitrary precision instead of declining; global promotion was implemented, measured against `axeyum-cas`, and rejected
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

**Exact rational arithmetic in the IR gains an arbitrary-precision slow path
behind the existing `i128` fast path, and promotion is OPT-IN PER ROUTE: a
parallel `wide_*` family promotes on `i128` overflow, while `new`, the
`checked_*` family and the arithmetic operators keep declining exactly as they
did before.**

The first draft of this ADR made promotion the global meaning of the existing
operations. That was implemented, measured, and rejected — see *The measurement
that changed this decision* below. What landed is the same machinery with a
narrower contract.

| family | on `i128` overflow | who uses it |
|---|---|---|
| `new`, `checked_new`, `checked_neg/add/sub/mul/div`, `recip`, and the `Add`/`Sub`/`Mul`/`Div`/`Neg` operators | **declines** (`None`) or panics — unchanged | everything, by default |
| `wide_new`, `wide_neg`, `wide_add`, `wide_sub`, `wide_mul`, `wide_div`, `wide_recip` | **promotes** to arbitrary precision | a route that opts in |

Detail:

- The public API of `Rational` does not change shape. Every pre-existing
  `pub fn` keeps its name, signature **and behaviour**, so the 223 files and
  ~5,500 references that consume the type are unaffected.
- `Rational` stays `Copy`. This is a hard constraint, not a preference: it is
  consumed by value in ~5,500 places and is a field of the interned
  `TermNode::RealConst`. `BigRational` is heap-owned and therefore not `Copy`,
  so the big representation is a **handle** into a process-global,
  deduplicating, append-only pool, encoded in the existing 32 bytes by the
  otherwise-impossible `den == 0` (the small invariant is `den > 0`). The
  struct's size and layout are unchanged, so the dense simplex tableau's
  memory model is unchanged.
- Any result that fits `i128` again is **demoted** back, on both families, so
  the fast path is retaken after transient growth and each value has exactly
  one representation — the canonicality `TermNode` interning depends on.
- The declining family **accepts** promoted operands: it computes exactly and
  then demotes, returning `None` if the result does not fit. A promoted value
  therefore never produces a wrong answer anywhere, only a decline.
- Comparison is the one operation that is not opt-in. `Ord::cmp` and
  `wide_cmp` are always exact and can never fail, because comparing allocates
  no pool entry; before this ADR `Ord::cmp` panicked on a cross-multiplication
  overflow. `checked_cmp` keeps its declining behaviour for two small operands
  so nothing that depended on it changes.
- The pool is capped (`Rational::big_pool_capacity()`, 2^20 distinct values).
  Past the cap, promotion fails and the `wide_*` family behaves exactly like
  the declining one. The cap is what keeps an append-only pool from turning a
  fast `unknown` into an out-of-memory.
- `Eq`, `Ord`, `Hash` and `Display` are **value-based and
  representation-independent**: the pool id is never observable.

### The first route to opt in: the simplex

`crates/axeyum-solver/src/simplex.rs` switches its five local arithmetic
helpers to the `wide_*` family, so intermediate coefficient growth inside the
tableau no longer abandons the search. Promotion is **contained** there: every
value leaving the module passes through a `narrow` guard that declines to
`Unknown` if a feasible point or a Farkas multiplier does not fit `i128`.
Nothing downstream — `lra`, `lra_online`, model lifting, certificate
serialization — can observe that a promoted value existed, which is what makes
the widening a pure gain rather than a new obligation on every consumer.

### Two slices

| slice | scope | lane |
|---|---|---|
| 1 | `Rational`'s two representations and the `wide_*` family, plus the simplex opting in | this ADR's lane (landed) |
| 2 | `Value::Int(i128)` in [`value.rs`](../../../crates/axeyum-ir/src/value.rs), the SMT-LIB integer-literal parser, and opting further routes in one at a time | a later lane; **not started** |

Slice 1 does not admit a single one of the 26 QF_UFLIA files. Those are
rejected at the *parser*, on `Value::Int(i128)`, before any `Rational` exists —
slice 2 is what admits them.

## The measurement that changed this decision

Global promotion — `checked_*` and the operators promoting rather than
declining — was implemented first, and it passed a lot: the whole workspace
compiled unchanged, `axeyum-solver --lib --features full` reached 1438/1438
after two call sites were fixed, the corpus sweep and all three z3 differential
fuzzes were green.

Then `cargo test -p axeyum-cas --lib` was run. **25 unit tests failed and about
seven more stopped terminating** (still running at 45 minutes, at full CPU,
where the whole suite takes 69 seconds). A controlled A/B on a named subset —
the same six tests, the same command, my tree versus a snapshot of the
pre-change commit — was 6 failed / 0 passed against 0 failed / 6 passed.

The cause is not incidental. `axeyum-cas` uses **`i128` exhaustion as a cost
bound and a termination argument**. Its Groebner reduction declines with
`Declined(Overflow)`, its Wilf-Zeilberger certificate search and its zero tests
decline when an intermediate leaves range, and its interval arithmetic declines
on an unnegatable endpoint. Remove that bound and the same computations run
away on values with hundreds of digits instead of stopping. Several failing
tests are named for the contract directly:
`an_overflowing_coefficient_declines_as_overflow_not_as_a_ceiling`,
`overflow_is_reported_as_unknown_not_wrong`, `a_refutation_is_not_a_decline`.

No magnitude ceiling rescues the global design, because those routes decline
*at* `i128` — the values in the failing assertions are 10^30 to 10^69, so any
ceiling loose enough to help the simplex is loose enough to break the CAS.

So `i128` range is load-bearing for one population of consumers and a liability
for another. One type cannot change its meaning to serve both. Making promotion
an opt-in family serves both exactly, at the cost of one extra name per
operation.

### The residual hazard, named and contained

`numerator()` and `denominator()` return `i128` and are called at 416 sites.
They keep that signature, and they **panic with a clear message** on a promoted
value. Saturating or truncating was rejected outright: it converts an
out-of-range value into a silently wrong one, which is the one failure mode
this project does not accept. New accessors give callers a non-panicking
route — `checked_numerator()`, `checked_denominator()` (both `Option<i128>`)
and `numerator_big()` / `denominator_big()` (`BigInt`) — plus `is_big()`.

Under the opt-in design this hazard is **contained by construction**: only a
route that calls `wide_*` can create a promoted value, and the only such route
is the simplex, which narrows at its own boundary. The 416 sites are therefore
unreachable from a promoted value today. Two of them were hardened anyway,
because the global-promotion experiment reached them and the fixes are right
either way: `nra_real_root::Sign::of_rational` now reads the sign from the
value instead of from `numerator()`, and `nra_handelman_cert` uses
`checked_numerator`/`checked_denominator` where it serializes `i128` pairs onto
the wire.

Every future opt-in must repeat that discipline: either keep promoted values
inside the route, or use the checked accessors at the boundary. That is the
per-route audit slice 2 inherits.

## Evidence

- Fast-path cost: the promotion test is `den > 0` on each operand — two
  compares on a value already in a register, ahead of arithmetic that is
  unchanged instruction for instruction. Measured against the
  `simplex_incremental_check_feasible_lp` and `arena_intern` criterion
  benchmarks before and after, pinned to `taskset -c 0-7`; the deltas are in
  the lane status file. A regression beyond the measured noise band was a
  blocking condition for landing.
- Property test: every `wide_*` operation compared against `BigRational`
  computed directly, over a seeded generator that deliberately straddles
  `2^127` and feeds promoted values in as *operands*, not just checking them as
  results. The same loop asserts the declining family never disagrees with the
  wide one — it returns the identical value or `None`, never a third answer.
- The discriminating test for this ADR's actual decision is
  `the_checked_family_declines_exactly_where_the_wide_family_promotes`: the
  same six operations, declining on one family and exact on the other. A patch
  that made `checked_*` promote would pass every other test in the file.
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
- **Promote globally, with a magnitude ceiling.** Rejected on the measurement
  above: `axeyum-cas` declines *at* `i128`, and the values in its failing
  assertions are 10^30 to 10^69, so no ceiling separates the two populations.
- **Promote globally and fix `axeyum-cas`.** The ~seven non-terminating tests
  are not test bugs; they are algorithms whose termination argument was the
  `i128` bound. Giving them explicit magnitude budgets is a real change to a
  79k-line crate's cost model and belongs in its own ADR, not smuggled in
  behind a numeric-type change.

## Consequences

- `simplex.rs`'s `Overflow` marker stays. It is **not** unreachable after
  slice 1: `wide_div` still returns `None` on division by zero, the `narrow`
  boundary declines a witness or certificate outside `i128`, and promotion
  still fails at the pool cap. Removing it would delete a live soundness path.
  The pivot and deadline budgets are untouched, so the simplex's termination
  and determinism arguments are unchanged.
- **`axeyum-cas` is unchanged and must stay that way** until someone gives its
  algorithms an explicit cost bound. Anyone tempted to make `checked_*` promote
  "since the machinery is already there" should run
  `cargo test -p axeyum-cas --lib` first: it is 69 seconds when the bound is
  intact and does not finish when it is not.
- The LRA atom cap does **not** move in slice 1, and slice 1 does not claim
  it. Turning that cap from a partial overflow guard into a pure memory bound
  is a follow-up that must be measured on its own.
- `axeyum-ir` gains a process-global mutable pool. It is the first one in the
  crate. It is documented as append-only and capped, and `big_pool_len()` is
  exposed so a test or a diagnosis can see it.
- Slice 2 (`Value::Int`, the parser, and the 416 accessor sites) is now
  unblocked and is the change that admits the 26 QF_UFLIA files. It landed on
  2026-09-06; see **Slice 2** below.

---

## Slice 2 (landed 2026-09-06): the integer literal, and why its shape differs

Slice 2 admits an integer literal wider than `i128` at the SMT-LIB front door.
All 26 QF_UFLIA files that carried EVM `uint256` bounds now parse and dispatch
instead of being refused before any solver work. The measured record is
[`docs/research/11-design-review/2026-09-06-s9-int-wide-measured.md`](../11-design-review/2026-09-06-s9-int-wide-measured.md);
the artifacts are under `bench-results/s9-int-wide-20260906/`.

### It is a sibling variant, not a two-representation payload

Slice 1's move was to keep `Rational`'s layout and put promotion behind an
opt-in family, so its ~5,500 by-value consumers were unaffected. That works
because `Rational` is a **struct**. `Value::Int` is an enum **variant**, and the
analogous "consumers stay correct by construction" move for a variant is a
second variant:

| | slice 1 | slice 2 |
|---|---|---|
| the type | `struct Rational` | `enum Value` / `enum TermNode` |
| keeping consumers correct | same layout, same signatures, promotion opt-in | a sibling variant the `i128` arms never match |
| the precedent | `WideUint`'s pool-handle trick | `Value::Bv`/`WideBv`, `BvConst`/`WideBvConst` |

So slice 2 adds `TermNode::WideIntConst(WideInt)` and `Value::WideInt(WideInt)`,
with `WideInt` a `num_bigint::BigInt` newtype in
[`crates/axeyum-ir/src/int_wide.rs`](../../../crates/axeyum-ir/src/int_wide.rs).
This is the design **ADR-0376 already recorded** for the day this widening was
justified, down to the payload type and the canonicality rule, and it is
recorded there because ADR-0376 had rejected the alternative on measurement:
changing `IntConst`'s payload breaks the `*value` deref at every match site and
turns every `arena.int_const(0)` on the hot LIA path into a heap allocation.

The `i128` sites end up with a **stronger** guarantee than slice 1's 416
accessor sites got. Slice 1's sites are safe because nothing creates a promoted
`Rational` unless a route calls `wide_*`; slice 2's ~390 `Value::Int` and ~210
`IntConst` sites are safe because they cannot pattern-match a wide value at all.
There is no truncation for them to get wrong.

`WideInt::to_i128` still carries slice 1's hazard contract verbatim: it returns
`i128` and **panics** rather than truncating or saturating, exactly as
`Rational::numerator` and `WideUint::to_u128` do, with `checked_i128` and `big`
as the non-panicking routes. `Value::as_int` returns `None` for a wide value.

### Canonicality is the invariant that has to hold

`TermNode` keys the arena's intern table and both enums derive `Hash`/`Eq`, so a
value with two representations silently breaks structural sharing. The rule:

> A well-formed `WideIntConst(w)` / `Value::WideInt(w)` satisfies
> `w.checked_i128().is_none()`.

It is enforced at the two constructors that build those nodes,
`TermArena::int_const_big` and `Value::from_wide_int`, both of which **demote**.
`int_const_big(5)` and `int_const(5)` return the same `TermId`, and the test
asserts that on `TermId` identity rather than on rendered text, because breaking
the invariant is silent: two nodes for one value still type-check and still
evaluate.

### The evaluator was a panic on user input, and that is what slice 2 fixes

`eval`'s `int_bin`/`int_cmp` and eleven sibling handlers read operands with
`as_int().expect("builder guaranteed Int operand")`. `as_int` is `None` for a
wide value, so admitting the literal without touching `eval` would have panicked
on a parsed `2^256` — on the one path every `sat` is replayed through. `eval`
now takes a wide-integer detour mirroring the wide-BV one already beside it: an
explicit `supports_wide_int_path` list (`Eq`, `IntNeg/Add/Sub/Mul/Div/Mod/Abs`,
the four comparisons) computes exactly in `BigInt`, and every other operator
declines with `IrError::Unsupported` **before** reaching the `expect`.

Narrow-by-narrow arithmetic is bit-for-bit unchanged, so `i128::MAX + 1` still
reports `ArithmeticOverflow` instead of quietly promoting. That is slice 1's
`axeyum-cas` lesson applied again: `i128` exhaustion is load-bearing for some
consumers, so promotion must be something a caller reaches for, never something
that happens to it.

### The audit was compile-driven

Adding the two variants broke **62 `match` sites across 13 crates**. That is the
second reason for the sibling shape: the compiler enumerates the audit, where a
payload change would have compiled at many of those sites and changed their
meaning. Every site was resolved as a decline or an exact rule, never a
narrowing — notably `IntInterval` bound extraction returns `None`, because
saturating a `2^256` bound into an `i128` interval would be a *wrong* bound, not
a coarse one.

### Nothing has opted in, and that is a measurement, not an omission

`Features::has_wide_int` is the opt-in point, and `wide_int_admission` declines
at the dispatch boundary with a named `unknown`. It changes no verdict — every
route already fails closed, and the LIA/LRA linearizers' wildcard arm plus
`ArithAbstractor::ensure_supported_atom` mean a wide-bearing atom is rejected at
abstraction time rather than becoming an opaque literal the CDCL(T) loop could
satisfy vacuously. What it changes is cost and explanation.

Opting a route in is out of scope for this slice, and ADR-0376's ablation —
re-run on today's HEAD before any code was written — is the reason. With every
wide literal *rescaled into range*, and again with every assert mentioning one
*deleted*, all six files cvc5 decides are still `unknown`. The binding
constraint on that population is the decision procedure, not the literal type,
so the parity plan's "+6 measured against cvc5" for row S9 is the count cvc5
decides and not a measured axeyum gain. The honest yield of slice 2 on QF_UFLIA
is the 26 files moving from *not attempted* to a first-class `unknown` on a
route that can now be improved, plus a representation that QF_LIA, QF_NIA and
the EVM/finite-field front ends need independently.
