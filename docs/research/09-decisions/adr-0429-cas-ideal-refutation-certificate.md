# ADR-0429: Multivariate ideal refutation certified by a polynomial identity

Status: proposed
Date: 2026-08-13

## Context

ADR-0386 gave `axeyum-cas` its first dependent: two refutation routes that
normalize an assertion with `MvPoly` and hand a certificate to an independent
expander. Its own standard is stated there and is the standard this ADR is held
to: *a CAS answer that cannot be re-checked is not evidence.*

Both ADR-0386 routes reason about **one** assertion at a time — one disequality,
one `k·m = c` equation. Nothing in the workspace reasons about the **ideal** a
system of asserted equations generates, and the machinery to do so has existed
unused since ADR-0301: `crates/axeyum-cas/src/groebner.rs`, Buchberger over ℚ,
with `groebner_basis`, `reduce` and `ideal_contains`.

Three measurements taken on this branch before any change.

**1. The supply side is not what it looks like.** The obvious reading of "wire
the CAS in" is Sturm sequences and real-root isolation. That capability is not
missing — it is *duplicated*. `crates/axeyum-solver/src/nra_real_root.rs` is
7684 lines of exact univariate sign-cell decomposition with `RealAlgebraic`
witnesses, resultant elimination for two-variable components and a bounded CAD
ladder above that; `axeyum-cas/src/sturm.rs` is 303 lines and strictly weaker.
The real gap is elsewhere.

**2. `ideal_contains` returns `Option<bool>`.** A bare bool. Turning it into a
verdict would require trusting Buchberger's algorithm, the `lex` leading-term
selection, `MvPoly`'s canonicalization and every exact-rational operation
underneath — precisely the oracle laundering ADR-0301 alternative (D) forbids.
`groebner.rs` contains zero occurrences of certificate/witness/proof vocabulary,
and `axeyum-cas` exposes no `verify`/`check_certificate` free function anywhere.

**3. What is actually undecided.** Measured with `check_auto_explained` at a 10 s
budget:

| query | verdict before | route that declined |
|---|---|---|
| `(/ p q) + (/ q p) = 3 ∧ (/ p q)·(/ q p) = 5` over ℝ | `unknown` 282 ms | `nra`: "3 cross-products exceed the deterministic admission bound of 2 … this needs a nlsat/CAD engine" |
| `x+y+z = 1 ∧ xy+yz+zx = 1 ∧ xyz = 1 ∧ x²+y²+z² ≥ 0` | `unknown` 11 ms | `nra-real-root`: "2-variable resultant elimination could not certify" |
| `(mod a b) + (mod b a) = 3 ∧ (mod a b)·(mod b a) = 5` | `unknown` 801 ms | `int-blast-ladder`: "no model within the bounded integer width 32" |
| `(div a b) + (div b a) = 3 ∧ (div a b)·(div b a) = 5` | `unknown` 1.24 s | same |
| the same with an asserted inequality | `unknown` 1.73 s | same |

The honest counter-measurement matters as much. `x + y = 3 ∧ x·y = 5` — the
smallest case the new reasoning closes — was **already decided**, by
`nra-real-root` in 0.96 ms over ℝ and by `int-real-relax` in 3.8 ms over ℤ. The
gap is not "systems of polynomial equations". It is systems whose atoms leave the
polynomial fragment (`div`, `mod`, `ite`, an uninterpreted application), where
`int-real-relax` aborts outright and `nra-real-root` declines on a non-polynomial
operator, plus systems past the CAD caps.

## Decision

**Add cofactor tracking to `axeyum-cas` so ideal membership emits a witness, and
add one solver route, `cas-ideal-refuter`, whose certificate is a polynomial
identity re-derived by a checker with no CAS dependency.**

1. **`crates/axeyum-cas/src/groebner_cert.rs` — the missing artifact.**
   Buchberger's algorithm run with every polynomial carrying its representation
   in the *original* generators, through all three places where the invariant
   must hold: the initial basis (`rep = eᵢ`), S-polynomials
   (`S.rep = f·A.rep − g·B.rep`) and the division loop. `reduce_with_cofactors`
   returns the exact identity

   ```text
   target = Σᵢ cofactorᵢ · generatorᵢ + remainder
   ```

   A zero remainder is ideal membership; a *constant* remainder `c` says
   `target ≡ c` modulo the ideal, which is the more useful half. Bounds are
   explicit step counts (`Limits`), never a clock.

   It deliberately does **not** trim to the reduced Gröbner basis: trimming would
   need its own representation bookkeeping for no gain, since reduction to zero
   modulo *any* Gröbner basis is already the membership test.

2. **`crates/axeyum-solver/src/cas_poly.rs::cas_ideal_refutation` — untrusted
   search.** Collects the asserted comparisons over one opaque-atom abstraction
   and tries three shapes, in order:

   * **unit ideal** — `Σ cᵢ·gᵢ = 1` for the asserted equations, the weak
     Nullstellensatz: no common zero over any field containing ℚ, hence none over
     ℝ and none over ℤ;
   * **squares modulo the ideal** — a sum of atom squares congruent to a
     *negative* constant. `x + y = 3 ∧ x·y = 5` is the smallest instance:
     `x² + y² ≡ 9 − 10 = −1`, and a sum of squares is never negative. Note that
     nothing in the query mentions `x² + y²`; the square terms are tautologies the
     certificate supplies, which is why no rewriting or blasting route finds this;
   * **an asserted inequality modulo the ideal** — normal form a constant its own
     comparison forbids.

3. **`crates/axeyum-solver/src/cas_certificate.rs::check_cas_ideal_certificate` —
   trusted small checking.** One certificate format covers all three. Each entry
   is either a cited top-level conjunct with a multiplier, or a tautological
   `coefficient · monomial` with every exponent even. The checker re-reads every
   cited conjunct off the assertion list, re-derives the fact from its comparison
   head (never from the certificate's label), re-expands with the ADR-0386
   expander that shares no code with `MvPoly`, and requires the sum to be a
   constant `k`. It refutes on exactly three conditions, each stated in the
   source: no inequality entries and `k ≠ 0`; `k < lower`; or `k = lower` with a
   real-sorted strict entry, where `lower` sums the multipliers of the
   integer-strict entries (`p > 0` over ℤ is `p ≥ 1`).

   Multipliers on inequality entries **must be strictly positive rational
   constants**. A polynomial multiplier can take a negative value and would flip
   the inequality; equality multipliers are arbitrary polynomials, which is what
   makes the format a Nullstellensatz certificate rather than a Farkas one.

4. **Placement is measured, not assumed.** The first placement — beside the two
   ADR-0386 routes at the top of `check_auto_with_recorder` — was a **regression**:
   `x + y = 3 ∧ x·y = 5` over ℝ went from 0.96 ms via `nra-real-root` to 3.96 ms
   via this route. Gröbner is a millisecond-scale computation and the ADR-0386
   routes are microsecond-scale, so the ADR-0386 placement argument does not
   transfer. The route now sits after `nra-real-root` declines on the real branch
   and after `nia-bounded-blast` on the nonlinear-integer tail, immediately before
   the width ladder. A query the existing engines decide never reaches it.

   One strictly-additive change accompanies this: a `Some(Unknown)` from
   `nra-real-root` is terminal for the real branch (`nra` below is never reached),
   so the route is offered that unknown before it is returned. Only an `unknown`
   is ever replaced, and only by a certificate-checked `unsat`.

5. **`unknown` stays first-class.** Every decline returns "no decision". A route
   with a candidate records a decline with a reason; a route with no candidate
   records nothing, so unrelated traces are byte-identical to before.

## Evidence

Before/after, same queries, same 10 s budget, `check_auto_explained`:

| query | before | after |
|---|---|---|
| real division atoms | `unknown` 282 ms | `unsat` 4.5 ms, `cas-ideal-refuter` |
| 3 coupled reals past the CAD caps | `unknown` 11 ms | `unsat` 38 ms |
| integer `mod` atoms | `unknown` 801 ms | `unsat` 83 ms |
| integer `div` atoms | `unknown` 1.24 s | `unsat` 60 ms |
| integer `div` atoms + inequality | `unknown` 1.73 s | `unsat` 80 ms |

Queries the existing engines already decide are unchanged and keep their route
and their timing, which is the point of the placement.

Negative controls, in `crates/axeyum-solver/tests/cas_ideal_route.rs`, all
asserted on the route's own outcome (`NotRefuted`, never `NoCandidate`) so none
can pass vacuously: a solvable near miss (`x·y = 2` for `x·y = 5`); a system
unsatisfiable over ℤ but satisfiable over ℝ, which the ideal argument must *not*
claim; a residue of the wrong sign; a residue exactly at the bound; a linear
system, which must not be a candidate at all. Eight tamper tests cover an
inflated multiplier, a relabelled constant, an **odd exponent** presented as a
square, a negative square coefficient, a truncated combination, a foreign
conjunct, a relabelled hypothesis kind and an empty combination.

Each control was verified to fire by mutation: with `check_cas_ideal_certificate`
stubbed to return `true`, all 8 tamper tests fail; with the two sign guards
mutated off, all 4 behavioural controls fail; with the nonlinearity admission gate
mutated off, the linear-system control fails. No control is a dud.

Gates: `axeyum-cas --lib` 572 passed; `axeyum-solver --lib --features full` 1121
passed; `cas_bridge_routes` 25; `corpus_regression` 1; `route_trace` 12;
`nia_tiny_witness` 4; `progress_frontier --features full` 9 of 9 including
`frontier_bv_reduction`. `clippy --all-targets --features full -D warnings` clean
on both crates.

### Amendment (same day): a fourth shape, and what the tamper tests were worth

**A fourth refutation shape.** A non-negative combination of asserted
inequalities, their **pairwise products**, and atom squares, collapsing to a
constant below its own floor. A product of two asserted non-negativities is
non-negative — a degree-2 fact no rational multiplier can express — carried by a
new `CasIdealEntry::AssertedProduct`.

The motivating shape is the Rado campaign's micro-lemma `M6`
(`M ≥ 1 ∧ w ≥ 1 ⊢ M·w ≥ M`), which its degree-3 lemma `L3` was hand-split into
after `L3` timed out at 60 s. Its refutation is
`(M − M·w) + (M−1)(w−1) + (w−1) = 0` against a floor of `1`.

Measured honestly: `M6` and `L3` in *minimal* form are already decided by
`int-real-relax` in about 1 ms on the pristine tree, so the campaign's timeout was
the monolithic hypothesis set rather than the shape. Where the product argument
adds reach is the same place the rest of the route does — atoms outside the
polynomial fragment:

| query | before | after |
|---|---|---|
| the `L3` shape over three `div` atoms | `unknown`, **20 s timeout** | `unsat` 207 ms |
| `M6` over real `/` atoms | `unsat` 60.6 ms via `nra` | `unsat` 1.2 ms |

The search is unit-coefficient over subsets of at most three candidates, so a
refutation needing `2x² + 3y²`, or a multiplier other than `1`, is still missed.
`reduce_many_with_cofactors` shares one Gröbner basis across all candidates.

**The tamper tests were mostly duds, and this was measured rather than assumed.**
Deleting the parity check, the citation check, the kind-label check, the
square-coefficient check, or either product guard left **every** tamper test
green. They all reject through the *identity* check — change any number and the
combination stops being a constant — so none exercised the guard it was named
after. Three product tamper tests were deleted outright: no forgery of their shape
can exist.

They are replaced by six **guard-isolating forgeries**. Each is a hand-built
certificate for a *satisfiable* query whose combination really is a constant of
the refuting sign, with exactly one guard standing between it and a wrong `unsat`.
The parity one is the clearest: `x³ = −1` is satisfiable at `x = −1`, and
presenting `x³` as a non-negative term cancels against the equation to give `−1`.

Verified 1:1 — each of the six guard deletions kills exactly one forgery, and only
that one.

One guard is measured **not** to be soundness-critical, and is documented as
conservative rather than load-bearing: an equality's polynomial is zero in every
model, so citing one as a product factor contributes zero, which is non-negative.
The rejection is kept for clarity; the honest note beats a control that tests
nothing.

## What this deliberately does not claim

The certificate is a statement about ℝ. It cannot see integrality:
`x + y = 3 ∧ x·y = 1` is unsatisfiable over ℤ and the route declines, correctly —
the system has real solutions `(3 ± √5)/2`. Closing that class needs a different
argument (integrality, congruence, or a bound), not a bigger Gröbner budget. The
control that pins this is `control_an_integer_only_unsat_is_not_refuted_by_the_ideal_argument`.

The search is incomplete in a second way: the square candidates are each atom
alone and all atoms together, with unit coefficients. Finding general
non-negative multipliers is a linear program over the residues, which is not
wired. A refutation that needs `2x² + 3y²` is missed today.

## Alternatives

- **Reuse `MvPoly` in the checker.** Rejected for the same reason ADR-0386
  rejected it: an `MvPoly` canonicalization bug would become a wrong-`unsat` bug.
  The whole value of the second expander is that it is a different algorithm
  written against the same specification.

- **Return `ideal_contains`'s bool and trust it.** Rejected — that is the
  laundering ADR-0301 forbids, and it is the reason cofactor tracking was built
  rather than a thin wrapper.

- **Keep the route on the ADR-0386 fast path.** Rejected on measurement: it took
  queries away from faster engines. See decision 4.

- **Allow polynomial multipliers on inequalities (full Positivstellensatz).**
  Rejected as unsound in this format without a positivity proof for the
  multiplier itself. A real Positivstellensatz route needs SOS search and is a
  separate decision.

- **Give the route a wall-clock budget.** Rejected: determinism is a public API
  promise. Every ceiling is a step, monomial, atom or generator count.
