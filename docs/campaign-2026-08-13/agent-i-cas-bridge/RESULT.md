# agent-i — wiring axeyum-cas into the solver

Landed: `119858e2c` (the bridge), `46fa155e3` (ADR-0429), plus a second round
adding the product shape and replacing the tamper tests. Branch `main`.

---

## Headline

The brief's framing — "we own Sturm sequences, Gröbner bases, positivity
certificates and interval arithmetic, and the solver cannot call them" — is
**half right, and the wrong half is the interesting one.**

Sturm sequences and real-root isolation are *not* a missing capability. The
solver has its own, and it is 25x larger and materially stronger than the CAS's.
What is genuinely missing is **ideal-theoretic reasoning about systems**, and
that is what got built: one new route, `cas-ideal-refuter`, with a certificate
that a checker re-derives without touching `axeyum-cas`.

Six named query classes went from `unknown` to `unsat`.

**And a soundness control did fail to fire — most of them did.** I measured it,
and it is the most useful thing in this report: see "The tamper tests were duds"
below.

---

## I1 — the capability/demand map

### Supply: what `axeyum-cas` provides

465 public functions, 28 public types, 0 public traits, across 27 modules
(counting method: exclude everything at/after each file's last column-0
`#[cfg(test)]`; 213 of the 465 are indented inside `impl` blocks and are invisible
to `grep '^pub fn'`, which is the ~10x undercount the brief warned about — seven
whole files have zero `^pub fn` and are 100% methods).

| CAS capability | file | solver route that could consume it | bridge before | bridge after |
|---|---|---|---|---|
| Gröbner basis, ideal membership | `groebner.rs` (3 fns) | QF_NIA / QF_NRA equation systems | **none** | **`cas-ideal-refuter`** |
| exact multivariate polynomial ℚ | `mvpoly.rs` (30 methods) | `cas-identity-refuter`, `cas-int-units` | ADR-0386 | + ideal route |
| Sturm real-root isolation | `sturm.rs` (3 fns) | `nra-real-root` | none | **still none — duplicate, see below** |
| real algebraic numbers | `algebraic.rs` (1 fn + 6 methods) | `nra-real-root` witnesses | none | **still none — duplicate** |
| exact rational interval arithmetic | `interval_arith.rs` (1 fn + 17 methods) | a bounded-box NRA refuter | none | still none — no consumer exists |
| number theory (gcd, factor, CRT, …) | `ntheory*.rs` (50 fns) | `cas-int-units` (`gcd` only) | 1 function | 1 function |
| integer factorization | `factor_int.rs` | `cas-int-units` `(a+1)·p = 1` decline | none | still none |
| Hermite / Smith normal form | `normalforms.rs` | LIA Diophantine systems | none | still none |
| Gosper / WZ summation | `gosper.rs` | no route consumes sums | none | still none |
| orthogonal polys, series, ratint, stats, sets, combinatorics, gfp, geometry, boolean, permutation, special, hyperbolic | 12 modules | **no solver route consumes any of these** | none | none |

**The duplication finding.** `crates/axeyum-solver/src/nra_real_root.rs` is 7684
lines: exact univariate sign-cell decomposition with `RealAlgebraic` witnesses,
resultant elimination for two-variable components, a bounded CAD ladder for ≥3
variables, and a syntactic SOS matcher with a `verify()`. `axeyum-cas/src/sturm.rs`
is 303 lines and does the univariate part only. So "wire Sturm into the solver"
would have been a downgrade. The `algebraic.rs` / `sturm.rs` / `interval_arith.rs`
trio is a *reimplementation gap*, not a capability gap — worth an ADR on which
copy survives, not a bridge.

### Demand: where the solver says `unknown` for reasons a CAS could settle

Measured on the pristine tree at a 10 s budget, `check_auto_explained`:

| shape | before | declining route + its own words |
|---|---|---|
| real `div` atoms in a 2-eq system | `unknown` 282 ms | `nra`: "3 cross-products exceed the deterministic admission bound of 2 … this needs a nlsat/CAD engine" |
| 3 coupled reals, non-strict conjunct | `unknown` 11 ms | `nra-real-root`: "2-variable resultant elimination could not certify" |
| integer `mod` atoms | `unknown` 801 ms | `int-blast-ladder`: "no model within the bounded integer width 32" |
| integer `div` atoms | `unknown` 1.24 s | same |
| integer `div` atoms + inequality | `unknown` 1.73 s | same |
| `ite` atoms | `unknown` 2.29 s | same |
| UF atoms, 3-var cubic | `unknown` 7.12 s | same |
| `(Array Int Int)` select atoms | `unknown` 114 ms | `array-fast-path` — outside the Bool/Int lazy array route; **still unknown**, see roadmap |

**The counter-measurement that changed the design.** `x + y = 3 ∧ x·y = 5` — the
smallest system the new reasoning closes, and the one I built the flagship test
around — was **already decided**: 0.96 ms by `nra-real-root` over ℝ, 3.8 ms by
`int-real-relax` over ℤ. So was the three-variable cubic system (1.4 ms). The gap
is not "systems of polynomial equations". It is systems whose **atoms leave the
polynomial fragment**, where `int-real-relax` aborts outright (`div`/`mod`/`abs`/
UF/arrays/quantifiers) and `nra-real-root` declines on a non-polynomial operator —
plus systems past `nra_real_root`'s CAD caps (`MAX_MULTI_SYLVESTER_DIM = 6`,
`MAX_CAD_CELLS = 256`).

Two demand instances the brief and the register name that this route does **not**
close, and should not:

- `x·y = 1 ∧ x + y = 3` (`tests/nia_tiny_witness.rs:91`) — unsat over ℤ, but the
  reals `(3 ± √5)/2` satisfy it. An ideal argument cannot see integrality.
- `x² + y² = 3` over ℤ (`tests/route_trace.rs:156`) — same class.

These need congruence or bound reasoning, not a bigger Gröbner budget. They are
the top roadmap item below.

---

## I2 — the bridge

### `crates/axeyum-cas/src/groebner_cert.rs` (new, 551 lines)

Buchberger with cofactor tracking. `ideal_contains` returned `Option<bool>` — a
bare bool, which under ADR-0386's own standard is not evidence. This carries every
polynomial's representation in the original generators through all three places
the invariant must hold, and returns

```
target = Σ cofactor_i · generator_i + remainder
```

exactly. Bounds are explicit step counts (`Limits`), never a clock.

### `crates/axeyum-solver/src/cas_poly.rs::cas_ideal_refutation` (search)

Three shapes, deterministic order: `1` in the ideal (weak Nullstellensatz); a sum
of atom squares congruent to a negative constant; an asserted inequality whose
normal form modulo the ideal contradicts its comparison.

The squares shape is the one that earns its keep. `x + y = 3 ∧ x·y = 5` is refuted
because `x² + y² ≡ 9 − 10 = −1` and a sum of squares is never negative — and
**nothing in the query mentions `x² + y²`**. The refutation needs a fact nobody
wrote down, which is why no rewriting or blasting route finds it.

### `crates/axeyum-solver/src/cas_certificate.rs::check_cas_ideal_certificate` (trusted)

One format for all three shapes. Entries are either a cited conjunct with a
multiplier, or a tautological `coefficient · monomial` with every exponent even.
The checker re-reads each conjunct off the assertion list, re-derives its fact from
the comparison head (never the certificate's label), re-expands with the ADR-0386
expander that shares no code with `MvPoly`, and requires the sum to be a constant
`k`. It refutes on exactly three conditions, each spelled out in the source. A
candidate that fails is `VerifierRejected`, never a verdict.

### Placement — the part I got wrong first

The first placement was beside the two ADR-0386 routes on the fast path. That was
a **regression**: the new route took `x + y = 3 ∧ x·y = 5` over ℝ from 0.96 ms
(`nra-real-root`) to 3.96 ms. Gröbner is millisecond-scale; the ADR-0386 routes are
microsecond-scale, so their placement argument does not transfer. Moved behind
`nra-real-root` and `nia-bounded-blast`. One strictly-additive change: a
`Some(Unknown)` from `nra-real-root` is terminal for the real branch, so the route
is offered that unknown before it is returned.

### What now decides that did not

| query | before | after |
|---|---|---|
| `(/ p q) + (/ q p) = 3 ∧ (/ p q)·(/ q p) = 5` over ℝ | `unknown` 282 ms | **`unsat` 4.5 ms** |
| `x+y+z = 1 ∧ xy+yz+zx = 1 ∧ xyz = 1 ∧ x²+y²+z² ≥ 0` | `unknown` 11 ms | **`unsat` 38 ms** |
| `(mod a b) + (mod b a) = 3 ∧ (mod a b)·(mod b a) = 5` | `unknown` 801 ms | **`unsat` 83 ms** |
| `(div a b) + (div b a) = 3 ∧ (div a b)·(div b a) = 5` | `unknown` 1.24 s | **`unsat` 60 ms** |
| the same with `(div a b)² + (div b a)² ≥ 6` | `unknown` 1.73 s | **`unsat` 80 ms** |
| the Rado `L3` shape over three `div` atoms | `unknown`, **20 s timeout** | **`unsat` 207 ms** |

Queries the existing engines already decide keep their route and their timing.

---

## Negative controls, and evidence each one fires

The brief's warning was exact: "four of five candidate negative controls did not
fire, so a carelessly chosen one passes while testing nothing." Every control here
asserts on the **route's own outcome** (`NotRefuted`, never `NoCandidate`), not on
the end-to-end verdict — because a query that stays `sat` proves nothing if the
route's admission gate rejected the shape before it looked.

Then each was verified by **mutation**: break the guard, confirm the test fails.

### Round one: the behavioural controls

| control | mutation applied | fired? |
|---|---|---|
| solvable near miss `x·y = 2` | both sign guards mutated off | **yes** |
| **ℤ-only unsat, ℝ-satisfiable** | " | **yes** |
| residue of the wrong sign | " | **yes** |
| residue exactly at the bound | " | **yes** |
| satisfiable product shape | " | **yes** |
| dropping a bound removes the product | " | **yes** |
| linear system is not a candidate | nonlinearity admission gate off | **yes** |

The one that matters most is the ℤ-only control (`x + y = 3 ∧ x·y = 1`): it pins
the fragment boundary. If the ideal argument ever claimed it, the identical
reasoning on the real-sorted query would be a wrong `unsat`.

### The tamper tests were duds — measured, not suspected

The eight tamper tests all failed when the whole checker was stubbed to
`return true`, which is what I first reported. That is a *weak* test: it only
shows the checker is called at all.

So I ran the strong version — delete **one guard at a time** and see which test
notices. The result:

| guard deleted | tamper tests that failed |
|---|---|
| even-exponent parity | **0** |
| square coefficient `> 0` | **0** |
| conjunct is actually asserted | **0** |
| kind label matches the conjunct | **0** |
| product factors are asserted | **0** |
| product multiplier is positive | **0** |
| stored constant matches re-derivation | 1 |

**Six of seven guards could be deleted with every tamper test still green.** They
all reject through the *identity* check — mutate any number in a real certificate
and the combination stops being a constant — so none of them exercised the guard
it was named after. Three product tamper tests were deleted outright: no forgery
of their shape can exist.

### Round two: six guard-isolating forgeries

Replaced with hand-built certificates for **satisfiable** queries whose
combination really is a constant of the refuting sign, with exactly one guard
between it and a wrong `unsat`.

| forgery | the satisfiable query it would wrongly refute | guard deleted → fires? |
|---|---|---|
| `x³` presented as non-negative | `x³ = −1` (`x = −1`) | **yes, and only this one** |
| `−x²` presented as non-negative | `x² = 1` (`x = 1`) | **yes, only** |
| `x > 0` relabelled as an equality (unlocking a negative multiplier) | `x > 0` over ℝ | **yes, only** |
| an unasserted `x ≤ 0` cited as a hypothesis | `x > 0` over ℝ | **yes, only** |
| a negative multiplier on a product | `x ≥ 2 ∧ x² = 2x+1` over ℝ | **yes, only** |
| an unasserted `x ≤ 0` as a product factor | same | **yes, only** |

Each of the six guard deletions kills **exactly one** forgery and no other. That
1:1 mapping is the evidence that every guard is load-bearing and every control
isolates its guard.

The parity forgery is the clearest: `x³ = −1` is satisfiable at `x = −1`, and
`x³ + (−1)·(x³ + 1) = −1` is a genuine constant of the refuting sign. Only the
even-exponent check stands between it and a wrong `unsat` — and `x³` is negative
exactly where the model is.

### One guard is measured *not* to be soundness-critical

The checker rejects an equality conjunct cited as a product factor. That
rejection is **conservative, not load-bearing**: an equality's polynomial is zero
in every model, so the product contributes zero, which is non-negative. No forgery
of that shape can exist, which is exactly why the test for it could never fire.
Recorded as such rather than shipped as a control that tests nothing.

## Gates

`axeyum-cas --lib` 572 passed · `axeyum-solver --lib --features full` **1121
passed** · `cas_bridge_routes` 25 · `corpus_regression` 1 · `route_trace` 12 ·
`nia_tiny_witness` 4 · `progress_frontier --features full` **9 of 9**, including
`frontier_bv_reduction` · `clippy --all-targets --features full -D warnings` clean
on both crates · `check-links.sh` ok. All counts nonzero and confirmed.

---

## I2b — the product shape, and what the Rado lemmas actually needed

Having landed the ideal route I went at the Rado obstacle directly. Route B's
blocker is "inequality lemmas of degree 3–4 in three variables", and its
micro-lemma `M6` (`M ≥ 1 ∧ w ≥ 1 ⊢ M·w ≥ M`) is the essence of the degree-3 lemma
`L3` that timed out at 60 s. `M6`'s refutation is

```
(M − M·w)  +  (M−1)(w−1)  +  (w−1)  =  0     against a floor of 1
```

and the middle term is a **product of two asserted bounds** — a degree-2 fact no
rational multiplier can express. So I added a fourth shape: non-negative
combinations of asserted inequalities, their pairwise products, and atom squares.

**Then I measured `M6` and `L3` on the pristine tree, and they were already
decided** — by `int-real-relax`, in about 1 ms each. The campaign's 60 s timeout
was the *monolithic hypothesis set*, not the shape; stated minimally, the solver
has had them all along.

Where the product argument does add reach is, again, opaque atoms:

| query | before | after |
|---|---|---|
| the `L3` shape over three `div` atoms | `unknown`, **20 s timeout** | `unsat` 207 ms |
| `M6` over real `/` atoms | `unsat` 60.6 ms via `nra` | `unsat` 1.2 ms |

The search is unit-coefficient over subsets of at most three candidates. A
refutation needing `2x² + 3y²` is missed — confirmed on a probe
(`x ≥ y ≥ 0 ∧ x² < y²` over `div` atoms needs coefficient 2 on a product and
stays `unknown`).

## I3 — the Rado `k = 3` case

**Not attempted end to end, and here is exactly where the obstacle sits.**

Route B's blocker (`docs/plan/proof-approaches-2026-08-12/route-b/REPORT.md:86-88`)
is "new inequality lemmas of degree 3–4 in three variables". The new route helps
with the *degree and variable count* — it is insensitive to both — but the Rado
lemmas are **inequalities over unbounded ℤ with a symbolic parameter**, and this
route's certificate is a statement about ℝ.

Concretely, the shape `b < a ∧ … ⊢ b·t³ ≥ a·b·t²` is refuted by an ideal
combination only if the negation's *real* relaxation is already unsatisfiable. When
it is, `int-real-relax` was already going to catch it. When it is not — which is
the interesting case, because the Rado lemmas are true over ℤ for reasons involving
integrality and the ordering — the ideal argument declines, correctly.

What the `k = 3` cases actually need is the third bullet of the roadmap below:
non-negative *polynomial* multipliers on the asserted inequalities
(Positivstellensatz), so that `b < a` can be multiplied by `t²` rather than only by
a positive rational. That is a bounded, well-defined next slice, and it is the
piece I would build next.

---

## Top three roadmap items

**1. An exact-rational LP over the residues — finish the positivity search.**
Products of asserted bounds are in (round two), but the search over them is
*unit-coefficient subsets of size ≤ 3*, which is a placeholder. The real problem
is small and completely standard: given the residues `rᵢ` of the candidate terms
modulo the ideal, find `λ ≥ 0` with `Σ λᵢ·rᵢ` constant and below the floor. That is
one LP feasibility question over ℚ. Measured miss:
`x ≥ y ≥ 0 ∧ x² < y²` over `div` atoms needs coefficient `2` on one product and
stays `unknown` today. `axeyum-cas/src/matrix.rs` has 27 unused methods that are
the right primitives, and the certificate format already accepts arbitrary
positive rational multipliers — only the *search* is missing.

**2. Integrality certificates — the class this route provably cannot reach.**
`x·y = 1 ∧ x + y = 3` and `x² + y² = 3` are the register's own named instances and
both stay `unknown`. Both are settled by a congruence argument (mod 4, mod 8) that
is exactly as re-checkable as a polynomial identity: exhibit a modulus `m` and show
the system's normal form has no solution in ℤ/mℤ by finite enumeration. `axeyum-cas`
has `gfp.rs` (11 unused functions) and CRT in `ntheory_more.rs`. This is the single
largest remaining nonlinear-integer hole and it has a small, self-checking witness.

**3. Resolve the Sturm/algebraic duplication before it drifts.**
`axeyum-cas/src/{sturm,algebraic,interval_arith}.rs` and
`axeyum-solver/src/nra_real_root.rs` are two implementations of the same
mathematics with different caps, different overflow behaviour and no shared tests.
`interval_arith.rs::abs()` can **panic** (`.expect("interval abs overflow")`,
lines 223-224) while every sibling operation returns `None` — a live divergence
from the module's own stated stance. Pick one implementation, make the other a
thin adapter, and cross-test them against each other; that is a differential
oracle we already own and are not running.

---

## Honest summary of value

- One new route with four refutation shapes; six named query classes from
  `unknown` to `unsat`; zero regressions.
- The soundness story is the honest one: 7 behavioural controls fire, 8 tamper
  tests were measured to be duds and were replaced by 6 forgeries that map 1:1
  onto the guards they test, and 1 guard is documented as conservative rather
  than load-bearing. **Testing that the checker is *called* is not testing that
  its guards are *needed*.** That distinction cost one extra measurement round
  and is the transferable lesson.
- The CAS's 465 public functions still have **one** consumer's worth of use:
  `MvPoly`, `ntheory::gcd`, and now `groebner_cert`. Twelve modules remain with no
  possible consumer in the current solver. That is not a bridge problem — those
  modules answer questions the solver does not ask.
- The most valuable thing measured today is negative: the brief's four flagship
  CAS capabilities are *three* duplications and one genuine gap. Building the
  genuine one was worth it; building the other three would have been a downgrade.
