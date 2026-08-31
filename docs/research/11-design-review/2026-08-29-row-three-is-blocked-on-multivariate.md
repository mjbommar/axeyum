# 19 of row 3's 28 are blocked on one thing: multivariate polynomial identity checking (2026-08-29)

**Measured by the lane that moved row 3 from 4 to 7 kernel-reconstructed**, and
re-verified against the ledger rather than inherited from the day-old review.

    cas-certificate: 35 total -- kernel-reconstructed 7, cas-internal 28

**The 28 did not shrink.** The three new facts are kernel-reconstructed
*siblings* of existing certificates, not reconstructions of them. Nothing was
relabeled. So the honest statement is: the certificates carry more
kernel-checked content, and the backlog the Pareto review named as "the specific
number to move" is unchanged at 28.

## The 28, and what each cluster needs

| cluster | n | blocker |
| --- | --- | --- |
| NRA geometry | 10 | **multivariate** polynomial identity checking |
| WZ (Wilf–Zeilberger) | 9 | **multivariate** polynomial identity checking |
| gf2 | 4 | GF(2) polynomial arithmetic, absent entirely |
| real-algebraic | 4 | (not sized this pass) |
| partial fractions | 1 | 3 of 4 coefficients are non-integer rationals; needs a `Rat.ofRat`-style cast that does not exist <!-- absent: Rat.ofRat --> |

**Every existing CAS→kernel bridge is explicitly univariate-only.** So a single
piece of infrastructure — multivariate polynomial identity checking over the
constructed rationals — unblocks **19 of 28**, two thirds of the backlog. That
is a far better shape than the review's framing suggested, which read as five
independent clusters.

## The qualification that survives regardless

The review already established, and it must not be lost when the number moves:
for many of these, reconstruction **relocates the modelling assumption rather
than discharging it**. Proving `Σ hᵢgᵢ = f` does not prove that those
polynomials mean the geometric predicates they are named after; the modelling
axiom becomes a kernel *definition choice* — better, not removed. A future
35-of-35 would still not mean what it sounds like, and each fact's notes have to
keep saying so.

## Why this is the right next investment

Row 3 is where the IVT/EVT graded family is thinnest against Mathlib. Rows 1 and
2 are strong: row 1 produces computed objects rather than existentials, and row 2
now has kernel theorems for both EVT and IVT plus a Heyting countermodel for the
underlying principle — an axis with no Mathlib counterpart at all. Row 4 does not
exist and cannot without adding axioms first. Row 3 is the one place where more
engineering directly improves the comparison, and two thirds of it is one
dependency.

## Related

- ADR-0601 (three producers, one trust anchor).
- `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`
- `docs/plan/status/274-cas-row-three.md` — per-fact sizing.


## CORRECTION (same day): "one dependency unblocks 19 of 28" is WRONG

The lane dispatched against this document measured the arities and refuted its
central claim. **Geometry and WZ need differently-shaped infrastructure.**

| cluster | arities | shape |
| --- | --- | --- |
| NRA geometry | **6–19 variables** | only **2 of 10** have constant cofactors; the other eight need polynomial × polynomial, up to a **324-term** cofactor in `simson-line` |
| WZ | **2–4 variables**, six of eight bivariate in `(n,k)` | the polynomial identity is only the certificate equation — Gamma-to-factorial modelling, boundary-term vanishing, and the induction on `n` are all separate |

**The fixed-arity alternative I suggested is refuted**: no small fixed arity
covers even two of the ten geometry certificates.

**And two of the ten carry a VACUOUS identity.** `varignon`'s conclusions are
both the zero polynomial with no generators; `thales`' single cofactor is `1`
against a conclusion byte-identical to its generator. They are the two cheapest
by term count *because there is nothing there* — exactly the shape that would
have been picked first as an easy win and scored as progress.

The real next piece is `prove_mul` (monomial × monomial): 8 more geometry
certificates, and a prerequisite for WZ. Second is the fractional-literal
`Rat.ofRat` cast, which unblocks `medians-concurrent` and the partial-fractions
row in one build.

**A correction to the inductive inventory quoted in briefs**, measured from
`kernel.environment()` rather than inherited: the list is **16**, and the
version circulating in briefs omits `Int` and `Rat` — both themselves
inductives, `Rat` being a two-field structure. So `Nat.Pair` is the only
*generic* product, not the only product-shaped declaration.
