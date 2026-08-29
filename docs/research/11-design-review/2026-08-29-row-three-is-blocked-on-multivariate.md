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
| partial fractions | 1 | 3 of 4 coefficients are non-integer rationals; needs a `Rat.ofRat`-style cast that does not exist |

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
