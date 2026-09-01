# ADR-1315: row 3 is cheap exactly where a DECISION PROCEDURE replaces a limit

Date: 2026-08-31
Status: Accepted
Lane: `row3-systematic`

Index-summary: A ranked survey of ADR-0603 row 3 (exact form on the decidable fragment) across the classical theorems this repository tracks, with two rows built -- the inverse function theorem and the irrationality decision -- and the remaining five candidates sized. The predictor of cheapness is not "is the CAS capability present" (every analysis theorem has a polynomial specialisation, so that ranks everything equally) but "does the classical proof's hard step become a DECISION". Two premises the lane started with were stale and are corrected: `CReal.integral_split` HAS landed, and `partial_fractions.rs` is not a row 3. The transferable finding is that a checker sharing its producer's ALGORITHM has unfalsifiable guards: 10 of 14 checks survive deletion in `inverse.rs` (shared Sturm layer) against 0 of 8 in `rationality.rs` (divisor enumeration against factorization).
Index-status: Accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
decided that a classical theorem lands as a four-row family: constructive
general form, boundary refutation, exact form on the decidable fragment,
labeled import. The Pareto argument rests on row 3 — row 1 is optimal *because*
row 2 refutes the general form while row 3 still settles the decidable one.

Before this lane, row 3 existed for four theorems, and one of them was not the
one the briefing believed. Measured by `grep -n 'ADR-0603' crates/axeyum-cas/src/*.rs`:

| theorem | file | marked row 3 |
|---|---|---|
| IVT | `real_algebraic.rs` (`polynomial_ivt`) | yes, in a comment on line 270 |
| EVT | `extremum.rs` | yes, module doc line 1 |
| MVT | `mvt.rs` | yes, module doc line 1 |
| Taylor + Lagrange remainder | `taylor.rs` | yes, module doc line 1 |
| **partial fractions** | `partial_fractions.rs` | **no — it carries no ADR-0603 marker at all** |

`partial_fractions.rs` is a CAS capability, not a graded-family row; the fourth
row 3 is IVT's, in `real_algebraic.rs`. Meanwhile `crates/axeyum-cas` is 53
modules and the ledger carried 47 `cas-certificate` facts, so the decision
surface really is much larger than four.

The question this ADR answers is which of the remaining classical theorems have
a row 3 that is *available and unbuilt*, and — more usefully — what predicts
that.

## Decision

**Rank row-3 candidates by whether the classical proof's HARD STEP becomes a
decision procedure, not by whether the supporting CAS capability exists.**

Every classical analysis theorem on the Spivak spine has *some* polynomial
specialisation, so "is the capability present" ranks almost everything equally
and is nearly useless as a guide. What separates a row 3 worth building from a
thin one is whether restricting to the decidable fragment turns the theorem's
actual difficulty into a *computation*, or merely evaporates it.

Three outcomes, and only the first is worth a lane:

1. **The hard step becomes a decision.** MVT's interior critical point becomes a
   Sturm-isolated root; EVT's attainment becomes a finite candidate comparison;
   the inverse function theorem's *well-definedness* becomes a Sturm count on
   the derivative; irrationality becomes a divisor enumeration. In each case
   there is something to compute, something to certify, and something a checker
   can get wrong.
2. **The hard step evaporates.** The FTC on rational polynomials is an algebraic
   identity: the antiderivative is exact, and the theorem is a polynomial
   equality check. Nothing is decided. A certificate for it would be a
   certificate that two polynomials are equal.
3. **The hard step stays hard.** FTA's row 3 needs complex root isolation, which
   is a genuinely missing algorithm rather than an assembly of existing pieces.

## The ranked survey

Verified against the tree on 2026-08-31, not inherited from the docs. Two of the
premises this lane started with were stale and are corrected below.

| # | classical theorem | row 3 status | what would decide it | rows 1/2 present? | verdict |
|---|---|---|---|---|---|
| 1 | **Inverse function theorem** (Spivak ch. 12) | **BUILT this lane**, `inverse.rs` | Sturm count of `p'` on `(a,b]` decides strict monotonicity, hence uniqueness of the preimage; `polynomial_ivt` names it | **both** — row 1 `CReal.inverse_lipschitz_of_pos_deriv`, row 2 the two kernel-computed counterexamples in `creal/ivt.rs` | highest value: the only family with rows 1 and 2 landed and row 3 empty |
| 2 | **Irrationality** (ch. 2, ch. 21) | **BUILT this lane**, `rationality.rs` | rational root theorem: enumerate `±n/d` from divisors of `a_0`, `a_n`, evaluate, and ask whether any root lies in the bracket | row 1 per-number only (`Nat.no_rational_sqrt_two`); row 2 is that deciding it over `CReal` decides `x = 0` | high: a genuine decidability contrast, and the checker shares NO algorithm with the producer |
| 3 | **FTA** (ch. 25–27) | not reachable | would need certified complex root isolation — 2-D bisection, or a resultant/Gröbner decomposition of `p(u+iv) = A + iB` | row 1 absent, row 2 **unassessed** (FTA is not obviously in IVT/EVT's constructive-failure class — it is stated over a compact set) | highest mathematical value, but a new algorithm, not assembly |
| 4 | **Radius of convergence for rational functions** (ch. 24) | available, unbuilt | pole location is a root-isolation problem, already solved by `sturm`/`factor_int` | neither row 1 nor row 2 exists; it would be a lone row | medium: real, but it would not close a family |
| 5 | **FTC / integral additivity** (ch. 13–14) | available, unbuilt, and **thin** | exact antiderivative of a rational polynomial; FTC I and II become polynomial identities | row 1 is **complete**, see the correction below | low: outcome 2 above — nothing is decided |
| 6 | **LUB** (ch. 8) | exists, narrow (`extremum.rs`, polynomial ranges only) | `algebraic_cmp` over a finite set of algebraic numbers generalises it trivially | rows 1 and 2 both landed (`CReal.supOn`; `CReal.lub_decides_em`) | low: the generalisation is a `max` over a list |
| 7 | **Boundedness** (ch. 7) | subsumed by `extremum.rs` | — | row 1 is fully constructive (`bounded_of_uniformly_continuous`, with a **computed** bound) | none: row 3 adds nothing when row 1 is already complete |

### Two corrections to premises this lane started with

- **`CReal.integral_split` HAS LANDED**, along with
  `CReal.integralSplitAnywhere` and `CReal.integralSplitArbitrary`
  (`shape_search --include-constructed --name-like integral_split`, verdict
  `FOUND 3`, over a freshly built index of 2,732 declarations). The Spivak
  spine's ch. 14 row still says additivity is "in progress" and blocked on two
  named facts; that is stale. This matters for the ranking: the FTC family's
  row 1 is not blocked, so a row 3 there would not be filling a hole.
- **`partial_fractions.rs` is not a row 3.** The briefing named it as one of
  four; it carries no ADR-0603 marker. IVT's row 3, in `real_algebraic.rs`, is
  the fourth.

## What was built

### Row 3 for the inverse function theorem (`crates/axeyum-cas/src/inverse.rs`)

`polynomial_inverse(p, a, b, y)` decides the classical hypothesis rather than
assuming it — `p'(a) ≠ 0`, `p'(b) ≠ 0`, and a Sturm count of zero for `p'` on
`(a, b]`, which together say `p'` has no zero anywhere on `[a, b]` — then names
the unique `x ∈ (a, b)` with `p(x) = y` as an `AlgebraicReal`, reusing
`polynomial_ivt` as a black box exactly as `mvt.rs` reuses
`polynomial_extremum`.

The content no sibling row 3 has is **uniqueness**. IVT names *a* root of a
sign-changing polynomial and says nothing about how many there are, which is
precisely what an inverse cannot tolerate.

Registered as `F:cas-inverse-quintic-degree-five-witness`
(`p = x^5 + x` on `[0, 2]`, `y = 3`, preimage named as a degree-5 algebraic
number), labeled `cas-internal`.

### Row 3 for the irrationality decision (`crates/axeyum-cas/src/rationality.rs`)

`decide_rationality` reads the verdict off the algebraic degree, i.e. off
`factor_univariate_over_q`. `verify_rationality_certificate` never factors
anything: it re-derives the verdict by the **rational root theorem**, with
checker-local trial-division divisor enumeration.

Registered as `F:cas-quintic-real-root-is-irrational` (the real root of
`x^5 - x - 1`), labeled `cas-internal`.

`distinct_propositions` moves **2254 → 2256**. The 12 pre-existing
`SHARED-DECLARATION-PAIR` failures in `check-proposition-duplication.py` are
unchanged and neither new fact is among them.

## Consequences, and the part worth carrying forward

**A checker whose producer shares its algorithm will have unfalsifiable guards,
and only deletion shows it.** Both checkers were written to the same standard.
Guard deletion in a `lane-snapshot.sh` scratch copy separated them sharply:

| module | checks | killed by exactly one test | killed by more than one | **survived** |
|---|---|---|---|---|
| `inverse.rs` (first draft) | 15 | 3 | 0 | **12** |
| `inverse.rs` (after repair) | 14 | 4 | 0 | **10** |
| `rationality.rs` | 8 | 3 | 5 | **0** |

`inverse.rs`'s module doc claimed nine independently-falsifiable guards. That
claim was false and deletion is what proved it: every fixture corrupted a
certificate in a way several checks reject, and whichever one remained caught
it. Each fixture was a real test of the checker; none was a test of *one* check.

The repair was not to delete overlapping checks — overlap in a certificate
checker is defence in depth — but to delete the *claim*, replace it with a
measured table of which check backs up which (itself measured, by deleting a
survivor together with its hypothesised backup), remove one check that could
never fail on its own, and rebuild one fixture so the check carrying the
module's actual mathematics is isolated.

`rationality.rs` has zero survivors because its checker and producer share no
algorithm — divisor enumeration against factorization. **That is the general
lever**: independence of *algorithm*, not merely independence of *call graph*.
`inverse.rs`, `mvt.rs` and `real_algebraic.rs` all share the Sturm layer between
producer and checker, and their guards overlap accordingly.

### Three findings about code these modules do not own

1. **`verify_ivt_certificate` and `verify_mvt_certificate` refuse a correct
   certificate whose witness is an exact rational.** `AlgebraicReal::refine`
   collapses its bracket to `lower == upper` when bisection lands on a rational
   root, so `(1, 1]` is a legitimate value representation — and a half-open
   Sturm count over it is `0`, never `1`. Both checkers require `lower < upper`.
   Fail-**closed**, so nothing unsound follows, but it is a false negative.
   Reproduced at `p = x^5 + x`, `y = 2` on `[0, 2]` (witness exactly `1`) and
   pinned by `inverse::tests::a_point_bracket_is_a_real_shape_and_the_sibling_checkers_refuse_it`,
   so fixing `real_algebraic.rs` turns a test red rather than passing silently.

2. **A real soundness bug in the rational-root enumeration, found by this
   module's own test on its first run.** The theorem's `n | a_0` clause is
   *vacuous* at `a_0 = 0` — every integer divides zero — so the divisor list
   comes back empty and the enumeration offers only the root `0`. For
   `p = x^2 - x` that loses the candidate `1`, which IS a root, and the checker
   would have accepted an `Irrational` verdict for a rational number. Fixed by
   stripping the `x^k` factor first; pinned end-to-end.

3. **A `checker_command` asserting ACCEPTANCE cannot detect a checker made too
   permissive**, and the break/restore run says so. Inverting
   `rationality.rs`'s in-bracket filter left the command at output 1, exit 0.
   Breaking the producer, and breaking the checker so it *rejects*, both moved
   it to output 0, exit 1. That direction is covered by the guard-deletion
   suite, not by the ledger's command — and it is worth stating in the evidence
   `notes` rather than leaving a reader to assume the command covers both.

### Row 3 is NOT already built wherever it is cheap

That was the honest alternative outcome this lane was asked to report if true,
and it is not true: two rows were available and unbuilt, both cheap, and one of
them (the inverse function theorem) is the single case where rows 1 and 2 were
both landed and row 3 was the only gap. What IS true is the narrower claim in
the ranking above: of the five remaining candidates, one is thin because the
theorem's content evaporates on the fragment (FTC), one is thin because row 1 is
already complete (boundedness), one is a trivial generalisation (LUB), one would
be a lone row (radius of convergence), and one — FTA — is genuinely hard and
needs an algorithm nobody here has written.

## References

- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — CAS evidence must
  reconstruct or be visibly `cas-internal`. Both new rows are `cas-internal` and
  say so in the module doc, the fact `notes`, the `axiom_footprint` and the
  evidence `notes`.
- [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
- [`docs/curriculum/graded-statement-families.md`](../../curriculum/graded-statement-families.md)
- [`docs/curriculum/foundational-books/spivak.md`](../../curriculum/foundational-books/spivak.md)
  — the ch. 14 row's "in progress" additivity claim is stale; see the correction
  above.
