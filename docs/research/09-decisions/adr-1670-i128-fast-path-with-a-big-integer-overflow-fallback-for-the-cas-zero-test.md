# ADR-1670: The CAS zero-test keeps its bounded normal form and gains an unbounded fallback; the coefficient type stays `Rational` at the API and stops being `i128` underneath it

Index-summary: CAS arbitrary precision — measured the `i128` wall, shipped an unbounded zero-test fallback with no public-type change, and priced the three migration options (71 public signatures, 33 public types, 18 cross-crate sites)
Index-status: proposed
Status: proposed
Date: 2026-09-05

## Context

[`docs/math-department/13-computer-algebra.md`](../../math-department/13-computer-algebra.md)
ranks **the arbitrary-precision core** first of its Next Ten, on the grounds
that five of the twelve chairs hit the `i128` wall "within minutes of real
use". The file records the wall as a property (`i128` rationals, overflow
reported as `ZeroTest::Unknown`) but not as a measurement: nobody had written
down *which* inputs fail and *at what size*.

The coefficient type is `axeyum_ir::Rational` — a pair of `i128`s with
`checked_*` arithmetic — and it is a workspace type, not a CAS type: the
solver and the IR use it too. `CasExpr::Const` holds one, `MultiPoly` maps
monomials to one, `MvPoly` likewise. Eight modules
(`telescoping`, `ratint`, `real_algebraic`, `mvpoly/big`, `sos/*`, …) already
grew their own `num-bigint` path beside the core, which is the duplication the
department file blames on this ADR's subject.

Two constraints shaped what could land now:

- **Five other lanes are concurrently adding modules against today's public
  API** (`enclosure.rs`, `qe.rs`, `numberfield.rs`, `geometry_beyond.rs`,
  `permgroup.rs`). Changing `CasExpr::Const`'s payload or `normalize`'s return
  type would break all five mid-flight.
- **`ZeroTest::Certified` promises a witness**, and the witness type is
  `MultiPoly` — bounded. A decision the engine can make is not the same as a
  certificate the type can carry, and conflating the two would weaken what
  `Certified` means.

## The wall, measured

Probe: a `#[test]` driving `normalize` and `equal` over binomial powers,
multinomial powers, rational-coefficient powers, Catalan-sized integer
coefficients, and rational functions. Run `--release` on the shared dev box,
`load average 31.7` — ADVISORY for timings, exact for verdicts (a verdict does
not move with load).

| input | `normalize` before | `equal` before | `equal` after |
|---|---|---|---|
| `(x+1)^130` | ok | — | — |
| `(x+1)^132` | **OVERFLOW** | — | — |
| `(x+1)^64 · (x+1)^64 = (x+1)^128` | ok | certified | certified |
| `(x+1)^80 · (x+1)^80 = (x+1)^160` | OVERFLOW | **UNKNOWN** | **certified** |
| `(x+1)^100 · (x+1)^100 = (x+1)^200` | OVERFLOW | **UNKNOWN** | **certified** |
| `(x+⅓)^80` | ok | — | — |
| `(x+⅓)^82` | **OVERFLOW** | — | — |
| `(x+⅓)^41 squared = (x+⅓)^82` | OVERFLOW | **UNKNOWN** | **certified** |
| `(x+⅓)^60 squared = (x+⅓)^120` | OVERFLOW | **UNKNOWN** | **certified** |
| Catalan series `Σ Cₖxᵏ`, deg 68 | ok | — | — |
| the same series **squared** | **OVERFLOW** | — | — |
| `(p+q)² = p²+2pq+q²`, `p` = that series | OVERFLOW | **UNKNOWN** | **certified** |
| `(x+1)^90 squared/(x+2) = (x+1)^180/(x+2)` | OVERFLOW | **UNKNOWN** | **certified** |
| `(x+1)^80 squared = (x+1)^160 + x³` (FALSE) | OVERFLOW | **UNKNOWN** | **refuted** |
| `(x+y+1)^70` | ok | — | — |
| `(x+y+1)^35 squared = (x+y+1)^70` | ok | certified | certified |
| `2·(x+1)^160 ≠ (x+1)^160` (TRUE inequality) | OVERFLOW | UNKNOWN | **UNKNOWN** |
| `√x·√x + (x+1)^80² = x + (x+1)^160` | OVERFLOW | UNKNOWN | **UNKNOWN** |
| `I² + 1 + (x+1)^80² = (x+1)^160` | OVERFLOW | UNKNOWN | **UNKNOWN** |
| `10¹⁸·10¹⁸·10¹⁸ = 0` | OVERFLOW | UNKNOWN | **UNKNOWN** |

Three facts the table settles that prose had not:

1. **The wall is not where the coefficients are large; it is where the
   *intermediates* are.** Multivariate expansion to degree 70 in three
   variables is fine, and so is the Catalan series whose largest coefficient is
   within a factor of four of the `i128` ceiling. What fails is *multiplying
   two things that each fit*.
2. **`C₆₉` cannot be spelled at all.** The 69th Catalan number is outside
   `i128`, so a combinatorics chair cannot write the *input*, never mind
   compute with it. No fallback inside the zero-test helps with that; only a
   coefficient-type change does.
3. **The bounded wall for a univariate binomial power is degree 131.** It is
   not a round number and it was not documented anywhere.

## Decision

**Ship the fallback; keep `Rational` as the public coefficient type; make the
zero-test's *internal* normal form unbounded. Do not migrate `CasExpr` or
`MultiPoly` in wave two either — migrate the witness instead.**

### What landed (this slice)

`equal_core` became two normal forms tried in order. `equal_core_bounded` is
the existing `i128` cross-multiplication, byte for byte. Only when it returns
`Unknown` does `equal_core_unbounded` run: the same `a·d − c·b` test over
`BigRatFunc`, a quotient of integer polynomials built on
`mvpoly::big::BigPoly` — the ring the multivariate GCD already computes in.

No rational coefficient type was introduced, because none is needed: a
constant `p/q` is the pair `(constant p, constant q)`, and a quotient of
integer polynomials already denotes every rational function the fragment can
spell. That is what let this reuse `BigPoly` rather than write a third
polynomial type; the additions to it are `constant`, `variable`, `add`, `neg`,
`pow`, `terms`, and a visibility widening from `pub(super)` to `pub(crate)`.

**No public signature and no public type changed.** The diff to `lib.rs` is
additive apart from renaming `equal_core`'s body to `equal_core_bounded` and
amending two doc comments.

Two declines are kept and documented rather than papered over:

- **Every `Unary` head is declined.** The bounded path atomizes `√u`, `|u|`,
  `root_q(u)`, `sin`/`cos`, `ln`, `exp`, `Jₙ` into variables and then relates
  those variables with six fold passes. The folds have no unbounded
  counterpart, and without them a *nonzero* normal form in atom variables does
  not prove `≠`. Half-deciding would be unsound; declining is not.
- **A refutation whose witness does not fit `i128` is declined.** The
  *decision* is available and the *certificate* is not. Emitting a polynomial
  that is not the difference would weaken `Certified`. Measured cost: exactly
  one row of the table (`2·(x+1)^160 ≠ (x+1)^160`).

One guard exists purely for soundness: the reserved imaginary unit `I` (and,
belt-and-braces, any name carrying the `\0` atom prefix) is declined on the
*inequality* branch, because `fold_imaginary` rewrites `I² = −1` and the
unbounded path does not. Without it, `I² + 1 + (x+1)^160 = (x+1)^160` — a
**true** identity — would be refuted. The equality branch needs no guard: a
zero polynomial is zero whatever its variables denote.

### The cost curve

`--release`, best of five per cell, on the shared dev box under
`load average 28.5`. **ADVISORY**: this box carried 42 concurrent `cargo`
processes during the run, so absolute times are inflated; the *ratios* are
between two measurements taken microseconds apart under the same load, which
is what makes them usable.

<!-- COST-CURVE -->

Read the three columns separately, because the obvious comparison confounds
two effects:

- **Same-algorithm product** spells `(x+1)^d` as an explicit `d`-fold product,
  so both rings perform the same `d − 1` polynomial multiplications. **This is
  the coefficient-ring number.**
- **Power** uses `Pow`, where `MultiPoly::pow` is repeated multiplication
  (`d` products) and `BigPoly::pow` is binary exponentiation (`⌈log₂ d⌉`
  squarings). The ratio mixes ring with algorithm. *Reported so the confound
  can be subtracted, not quoted on its own.*
- **Whole zero-test** additionally includes the bounded path's atom dictionary
  and six fold passes, which the unbounded path does not run at all. Also not a
  ring measurement.

### Why not the other two options

**(b) Migrate `CasExpr`/`MultiPoly` to `BigRational` wholesale.** Priced by
grep, using the trust registry's brace-aware scanner rather than a line count:

| surface | count |
|---|---|
| `axeyum-cas` public `fn`s whose signature names `Rational` | **71** of 760 |
| `axeyum-cas` public `struct`/`enum` definitions carrying `Rational` | **33** |
| files carrying at least one such signature | 23 |
| cross-crate call sites naming an `axeyum_cas` item together with one of the affected types | **18** |

That count understates the work, because `Rational` is `Copy` and
`BigRational` is not: every `*coeff`, `.copied()`, and by-value `Rational`
argument in those 71 signatures is a clone decision, not a type substitution.
And `Rational` lives in `axeyum-ir`, shared with the solver — so (b) is not a
migration of one crate's type but the introduction of a *second* coefficient
type into a crate whose public surface is built around the first.

**(c) Make the coefficient ring generic.** Strictly larger than (b): it turns
each of the same 71 signatures generic *and* pushes monomorphization into
every consumer, `axeyum-py` included. It buys flexibility this crate has not
demonstrated a need for — there is one bounded ring and one unbounded ring, not
a family.

**(a) as shipped, but understood correctly.** The measurement changes what (a)
means. The cost curve does not show a fast bounded path worth protecting with
a slow unbounded fallback; the unbounded ring is not the expensive one. So the
right architecture is not "bounded fast path, big fallback for the rare
overflow" — it is **`Rational` at the API boundary, unbounded underneath it**,
with the bounded form kept only where it is genuinely cheaper.

## Consequences

- `equal` decides strictly more than it did, and refuses strictly nothing more.
  Every conversion in the table above is a test named for its input; every
  remaining decline is a test too, with a positive control of the same shape
  below the wall, so each decline is demonstrably about width rather than
  about the head.
- The fallback runs only on inputs the bounded path returned `Unknown` for, so
  it cannot alter a verdict that already decided. Two negative controls pin
  this: verdict agreement across a twelve-entry corpus run through *both* paths
  directly, and byte-identical `equal_core` results (witness included) whenever
  the bounded path decided.
- `normalize` and `expand` are **unchanged** — they still return `None` on
  overflow, because their return types are the bounded ones. A caller who
  wants `(x+1)^132` expanded still cannot have it. This slice moved the
  zero-test, not the normal form.
- The `cas-certificate` trust registry is unaffected: no public function was
  added, `ZeroTest` was already in the certificate vocabulary, and the gate
  reports the same floor (54 certified, held).

## What wave two must do first

In this order, because each step is blocked by the one before it:

1. **Give the witness somewhere to live.** The one measured decision the
   engine can make and the API cannot express is a refutation whose difference
   exceeds `i128`. Until `ZeroTest` can carry an unbounded witness, every
   further unbounded capability runs into the same wall at the same place. The
   cheapest honest shape is a second `Certified`-strength variant carrying a
   big polynomial, not a wider `MultiPoly` — widening `MultiPoly` is option (b)
   through the back door.
2. **Port the six folds to the unbounded ring**, which is what unblocks
   `√`, `|·|`, `root_q`, Pythagorean, Bessel and `I` at overflow scale. This is
   the largest single gain left: the fold set, not the coefficient width, is
   what confines the fallback to the plain rational-function fragment.
3. **Make `MultiPoly::pow` binary.** Repeated multiplication is `d` products
   where `⌈log₂ d⌉` squarings suffice; the unbounded path already does this.
   Free, ring-independent, and it moves the bounded wall out on its own.
4. Only then revisit whether `CasExpr::Const` should change at all. The
   Catalan-`C₆₉` row is the one problem in the table that nothing short of a
   coefficient-type change fixes, and it is an *input* problem — which means it
   can be solved at the parser/constructor boundary rather than by rewriting
   71 signatures.

## Evidence

- Implementation: `crates/axeyum-cas/src/lib.rs` (`equal_core`,
  `equal_core_bounded`, `equal_core_unbounded`, `BigRatFunc`,
  `normalize_rational_big`, `multipoly_from_big`),
  `crates/axeyum-cas/src/mvpoly/big.rs`.
- Tests: `bignum_overflow_fallback` in `crates/axeyum-cas/src/lib.rs`.
- Department file this closes item 1 of:
  [`docs/math-department/13-computer-algebra.md`](../../math-department/13-computer-algebra.md).

<!-- GATES -->
