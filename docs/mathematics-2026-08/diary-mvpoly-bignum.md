# Lane diary: `mvpoly-bignum`

**Date:** 2026-08-14. **Predecessors:** `telescoping-scale` and `geometry`, which
hit the same wall from two directions and handed it over.

---

## 1. What actually failed

Two lanes reported that `crates/axeyum-cas/src/mvpoly.rs` was the blocker. Only
one of them could say why, and it was right.

The telescoping lane's finding: Apéry's summand `∑_k C(n,k)²·C(n+k,k)²` declines,
the derived degree bound is **2**, and the certificate exists at exactly `dx = 2`
with Apéry's own recurrence (verified out of tree in SymPy). So the *search
design* was never at fault; `MvPoly::gcd` overflowed `i128` on the degree-8 shift
quotient.

I reproduced that before changing anything, and the reproduction is the sharpest
thing in this diary:

```
  rho.num                terms    42  totdeg   8  maxcoeff  120
  rho.den                terms    32  totdeg   8  maxcoeff   18
  rho REDUCE OVERFLOW (gcd)
```

**The inputs' largest coefficient is 120.** The answer's largest coefficient is
6. And an `i128` — 127 bits, thirty-eight decimal digits — could not hold what
happened in between. The bound that bound was not on the question and not on the
answer. It was on the scratch space.

`MvPoly::gcd_cost` now measures exactly that, and the number is 4187 bits.

---

## 2. The fix, and why this one

Two candidates were offered: a subresultant PRS, or bignum coefficients. I took
**bignum coefficients, confined to the GCD**, in a new private module
`crates/axeyum-cas/src/mvpoly/big.rs`. `MvPoly::gcd` converts both inputs to a
`BigInt`-coefficient polynomial, runs the same recursive primitive PRS there, and
converts only the answer back. Nothing else about `MvPoly` changes: the public
type still holds `Copy` `i128` rationals, every other operation is still checked,
and the 163 call sites in two crates are untouched.

Three reasons for that choice over the subresultant PRS, in order of weight:

1. **A subresultant PRS postpones the failure; unbounded coefficients remove
   it.** Subresultant growth is polynomial rather than exponential, but it is
   still growth: a large enough input still overflows a fixed-width type, and the
   decline is still a fact about `i128` rather than about mathematics. Given that
   the geometry lane's whole complaint was that it could not tell an arithmetic
   failure from a budget failure, shipping a *smaller* arithmetic failure was the
   wrong shape of answer.
2. **The measured swell is intermediate, not terminal.** Inputs 120, answer 6,
   scratch 4187 bits. Only the scratch ring needs to be unbounded, so the cost of
   generality is confined to one algorithm rather than paid by the whole crate.
3. **`MvPoly::gcd` has three callers, none of them the Gröbner path.**
   `telescoping.rs`, `telescoping_check.rs`, `lib.rs::reduced_multivariate`. The
   geometry/Gröbner code uses `mul`/`add`/`sub` only, so a bignum GCD cannot slow
   the 247–365 s reductions the geometry lane was worried about. A wholesale
   bignum `MvPoly` would have, and `BigRational` normalizes on every operation.

There is a subresultant-shaped idea in the fix anyway, and it turned out to
matter more than the width: the pseudo-remainder loop now divides the **integer
content back out at every step** rather than only at the end. That is sound
because the caller uses only the primitive part, and it is what keeps the
bignums small — 4187 bits becomes 76.

`MvPoly::normalized` moved to the same ring while I was there, which also deletes
the `integer_gcd`/`integer_lcm` `i128` helpers and the four now-superseded PRS
methods. Net: `mvpoly.rs` is ~150 lines shorter.

### The honest caveat

76 bits is under 127. So an `i128` primitive PRS **with per-step content
division** would probably also have found Apéry. I did not verify that (it would
mean building a third implementation to test a counterfactual), and I would make
the same call again: the per-step division is a heuristic that shrinks the
constant, and the next summand up will exceed 127 bits with it in place, exactly
as this one did without. What is measured is that the old sequence needed 4187
bits and the new one needs 76; what is *not* claimed is that only the width fix
mattered.

---

## 3. Apéry

```
sum_k C(n,k)^2*C(n+k,k)^2  (Apery, order 2)  order 2  search  97.0ms  check  31.0ms  verified
```

The recurrence that comes back:

| | found | Apéry's |
|---|---|---|
| `a_0` | `n³ + 3n² + 3n + 1` | `(n+1)³` |
| `a_1` | `−34n³ − 153n² − 231n − 117` | `−(2n+3)(17n²+51n+39)` |
| `a_2` | `n³ + 6n² + 12n + 8` | `(n+2)³` |

Coefficient for coefficient. Verified by `telescoping_check`, which shares no
code with the search, and separately replayed against the Apéry numbers
`1, 5, 73, 1445, 33001, 819005, 21460825` in `i128`.

One detail of the acceptance is load-bearing and was **not** a free win. The
first check run rejected:

```
G is not evaluable at the window edge (k=-2, n=0)
```

That is the checker being right. At `n = 0` the summand is not evaluable at a
negative `k` — `C(n+k,k)` becomes `C(-1,-1)` — so a window starting at `k = -2`
asks the checker to evaluate something undefined, and it refuses rather than
guessing a zero. The window starts at `k = 0` instead; the certificate numerator
carries a factor `k⁴`, so `G` still vanishes at that edge, which is what the
boundary layer actually needs. I mention it because "adjust the check window
until it passes" is precisely the move that would turn this checker into
decoration, and the reason this particular adjustment is legitimate has to be
written down rather than assumed.

Apéry is now committed evidence, not a line in a report:
`artifacts/cas-certificates/apery-numbers-recurrence.json`, written by the
checker-gated emitter, re-checked from the file by a sweep that never calls the
search, and carried by `F:apery-numbers-recurrence`. The fact says only the
recurrence. The irrationality of `ζ(3)` is **not** claimed: that needs the second
solution of the same recurrence and a growth estimate, and this route produces
neither.

### Search cost, before and after

Same identities, same box, best of seven runs each, both binaries pinned to cores
0–7 (the "before" binary built from a clean `git archive HEAD` snapshot, so this
is a real A/B and not a memory of an earlier number):

| identity | before | after |
|---|---|---|
| `∑_k C(n,k)` | 1.22 ms | 1.54 ms |
| `∑_k (−1)^k C(n,k)` | 0.39 ms | 0.49 ms |
| `∑_k C(n,k)²` | 4.07 ms | 4.94 ms |
| `∑_k k·C(n,k)` | 1.34 ms | 1.68 ms |
| `∑_k C(m,k)C(n,p−k)` | 44.66 ms | 49.05 ms |
| `∑_k C(n,k)³` (Franel) | 101.80 ms | 119.80 ms |
| `∑_k C(m,k)C(n,k)` | 10.31 ms | 12.83 ms |
| **`∑_k C(n,k)²C(n+k,k)²` (Apéry)** | **declined** | **97.02 ms, verified** |

So: **1.10–1.26× slower on everything that already worked, and one identity that
did not work now does.** Checker times are unchanged to within noise. That is the
trade, stated plainly; I did not find a way to have the range for free, and the
constant is small enough that nothing in the corpus moves category.

### Coefficient growth, before and after

The second table of `examples/telescoping_search_cost.rs` reports it per
identity. `was` is the peak of the *same* sequence with the per-step content
division switched off — i.e. what the previous `i128` primitive PRS actually
computed — so `was > 127` is a measurement, not an inference, that the old code
could not have finished:

| identity | order | in | was | peak | out | steps |
|---|---|---|---|---|---|---|
| `∑ C(n,k)²` | 2 | 7 | 27 | 9 | 3 | 77 |
| `∑ C(n,k)³` (Franel) | 2 | 11 | 81 | 13 | 5 | 181 |
| Chu–Vandermonde | 2 | 3 | 16 | 7 | 2 | 323 |
| **Apéry** | 1 | 4 | **1412** | 22 | 2 | 93 |
| **Apéry** | 2 | 7 | **4187** | 76 | 3 | 153 |

Franel at 81 bits is the control: it is the deepest identity that *did* work
before, and it fits under 127 with nothing to spare. Apéry is 33× past the line.

---

## 4. `Declined` was one value for two failures

The geometry lane could not say whether `rhombus-diagonals-perpendicular` hit a
ceiling or an overflow, and — to its credit — recorded "not established" instead
of guessing. That is now a two-line change for anyone who asks.

`CofactorOutcome::Declined` carries a `DeclineReason`:
`ReductionSteps`, `PairIterations`, `BasisSize`, `PolyTerms`, `Overflow`, with
`is_ceiling()` drawing the line that matters (a ceiling is worth retrying with a
bigger budget; an overflow is not). Every `?` on an `MvPoly` or `Rational`
operation in `groebner_cert.rs` now goes through `Budget::arith`, which attributes
a `None` to `Overflow`; every ceiling records itself at the point it trips. The
attribution is exhaustive rather than a guess about which failure came first, and
the *first* reason wins because later ones are consequences.

Two controls, one per side of the split:
`a_tight_budget_declines_rather_than_guessing` now asserts `ReductionSteps`
specifically, and a new test reduces `x²` modulo `x − 10³⁰` — whose remainder is
`10⁶⁰`, past `i128` — and asserts `Overflow` with every budget barely touched,
plus that the same shape with a small coefficient reduces fine. Without the
second test the distinction would be documentary.

It propagates outward: `ProofOutcome::Declined(GeometryDecline)` distinguishes a
reduction decline (carrying the reason) from `TooManyConditions` and from
`UnverifiedWitness` — the last being a *refusal*, not a resource limit, and worth
keeping visibly separate from the other two. `geometry_probe` prints
`DECLINED (ceiling: PairIterations)` or `DECLINED (overflow: Overflow)`. And in
the solver, `cas_poly.rs` used to return the fixed string "hit a deterministic
step ceiling" for both cases; it now names the actual cause, because a reader
tuning `ideal_limits()` in response to an overflow is tuning the wrong knob.

`TelescopingOutcome::Declined` is deliberately **not** split. Its declines are
mostly "searched the whole space and found nothing", which is neither a ceiling
nor an overflow, and the one case where the distinction mattered — the GCD — no
longer declines. Splitting it would have been symmetry, not information.

---

## 5. Degree-reverse-lex

The geometry lane's structural suspect was the pure lexicographic monomial order:
worst for computing a basis, best for elimination, and ideal membership needs no
elimination. It is right, and it is now measurable rather than argued.

`MonomialOrder::{Lex, DegRevLex}` is a field on `groebner_cert::Limits`. Both are
well-orders compatible with multiplication, which is the only property
`Buchberger`'s termination and the division loop use, so the order can change the
cost and cannot change the answer. Four unit tests pin `grevlex` against the
Cox–Little–O'Shea examples (including the pair where it and `lex` disagree, which
is the point), and one control runs the same three-variable cubic system under
both orders and asserts the same membership verdict and an exact cofactor
recombination under each.

On the corpus that already certifies (release build, unpinned, one run each):

| theorem, condition subset | `lex` | `grevlex` |
|---|---|---|
| `thales-right-angle-in-semicircle` `{}` | 59.8 µs | 65.4 µs |
| `orthocentre-altitudes-concurrent` `{}` | 13.6 ms | 10.2 ms |
| `medians-concurrent` `{}` | 70.0 ms | 31.7 ms |
| `centroid-divides-medians` `{}` | 59.3 ms | 37.8 ms |
| `centroid-divides-medians` `{abc-not-collinear}` | 157.8 ms | 96.0 ms |
| `parallelogram-diagonals-bisect` `{}` | 9.0 ms | 9.2 ms |
| `parallelogram-diagonals-bisect` `{abd-not-collinear}` | 208.3 ms | 144.0 ms |

Same verdicts, same cofactor term counts, **1.3–2.2× faster** on everything that
costs anything. The defaults are unchanged for now — `geometry_limits()` and the
solver's `ideal_limits()` both still say `Lex` — because the committed geometry
certificates are evidence and their cofactors would change; switching the default
is a separate, deliberate landing with a regeneration of the artifacts.

### The frontier, with the reason attached — and one theorem crossed it

Two runs of `geometry_probe` on `rhombus-diagonals-perpendicular`, release build,
budget scale 1, the same ceilings both times:

| condition subset | `lex` | `grevlex` |
|---|---|---|
| `{}` | 6.0 s, not in ideal | 1.3 s, not in ideal |
| `{abd-not-collinear}` | **DECLINED (ceiling: `ReductionSteps`) after 287.8 s** | **IN IDEAL, 34 cofactor terms, 23.6 s** |

Two separate findings there, and the first one is the negative result the brief
asked for either way.

**The rhombus never overflowed.** It ran out of the 50 000-step reduction
budget. The geometry lane suspected `i128` and was careful to record that as
unestablished; it is now established, and it is **not** `i128`. So the change
this lane made for the GCD would not have moved this theorem at all, and the
lane that suspected it would have spent a week widening the wrong type. That is
what §4 is for, and it paid for itself on its first use.

**And `grevlex` reaches it.** A frontier theorem is no longer on the frontier:
same ceilings, same question, 34 cofactor terms, twelve times faster than the
`lex` run that gave up. Together with the 1.3–2.2× on the corpus, that is the
geometry lane's hypothesis confirmed with more force than it claimed.

I did **not** promote the rhombus into the corpus or switch the default, and the
reason is specific rather than cautious: `certify` returns the certificate for
the *smallest condition subset that succeeds*, so a faster order can change
**which non-degeneracy conditions a certificate uses** — and those conditions
appear as hypotheses in the facts' `formal.statement`. Regenerating six
committed certificates under a new order is therefore a change to what six facts
*claim*, not a re-render of how they are computed. That belongs to the lane that
curates the geometry corpus, with this measurement in hand and a degenerate
witness stated for the rhombus.

### `euler-line`: still out of reach, under both orders

The negative result the brief asked for either way. Two runs, `lex` and
`grevlex`, both pinned, both at budget scale 1, both given **1200 s**: neither
printed a verdict for even the **empty** condition subset. The geometry lane
recorded "no verdict within 600 s"; doubling the wall clock and changing the
monomial order does not change that.

So `grevlex` is not a general solvent. It moved the rhombus — a 3-hypothesis,
8-coordinate system — from declined to certified, and it does not visibly dent a
4-hypothesis, 10-coordinate one. Whatever `euler-line` needs, it is not this
lever, and the next lane should not spend a session assuming otherwise. The
right next measurement on it is which of the two the reduction is bound by, and
that is now one field on the outcome rather than a bisect.

---

## 6. What this lane did not do

- **Did not make `MvPoly` bignum.** Only the GCD ring. `mul`, `add`, `divide` and
  `evaluate` still overflow at `i128`, and the Gröbner path lives entirely in
  those. If a geometry reduction turns out to be overflow-bound rather than
  ceiling-bound, that is the next module to move — and thanks to §4, "turns out
  to be" is now a thing you can read off a run rather than infer.
- **Did not switch the default monomial order.** Measured, argued, left off.
- **Did not touch the `leading_integer_zeros` limitation** the telescoping lane
  named (declines when the leading recurrence coefficient mentions more than the
  shift variable; a Saalschütz-type identity will hit it). Unrelated to the
  coefficient type; still open.

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/mvpoly/big.rs` | the unbounded-integer ring the GCD computes in; the primitive PRS, moved wholesale |
| `crates/axeyum-cas/src/mvpoly.rs` | `gcd`/`normalized` delegate to it; `GcdCost` and `gcd_cost` are the measurement |
| `crates/axeyum-cas/src/groebner.rs` | `MonomialOrder`, `grevlex_cmp`, `leading_term_in` |
| `crates/axeyum-cas/src/groebner_cert.rs` | `DeclineReason`, the `Budget::arith` attribution, the order knob |
| `crates/axeyum-cas/src/geometry_certify.rs` | `GeometryDecline` |
| `crates/axeyum-solver/src/cas_poly.rs` | the decline message stops lying about ceilings |
| `crates/axeyum-cas/examples/telescoping_search_cost.rs` | the growth table |
| `crates/axeyum-cas/examples/geometry_probe.rs` | `AXEYUM_MONOMIAL_ORDER`, declines with causes |
| `crates/axeyum-cas/tests/telescoping_identities.rs` | `apery_numbers_get_aperys_own_recurrence` |
| `artifacts/cas-certificates/apery-numbers-recurrence.json` | the certificate |
| `artifacts/facts/F-apery-numbers-recurrence.json` | the fact |
