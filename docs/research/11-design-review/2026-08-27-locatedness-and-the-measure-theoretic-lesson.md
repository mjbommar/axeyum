# Locatedness, measure theory, and what our integral will keep fighting

Date: 2026-08-27. Companion to
[the architecture review](2026-08-27-architecture-review.md) §2 and to
ADR-0603's graded statement families.

## 1. Measure theory's motive was limits, not constructivity

Lebesgue integration exists because **Riemann integration is not closed under
limits**: pointwise limits of Riemann-integrable functions need not be
integrable, and where they are, `∫lim` need not equal `lim∫` without uniform
convergence. Dominated convergence is the payoff. That story is classical
throughout and has nothing to do with constructive scruples.

**But the structural consequence is exactly what cost us a day.** Measure
theory replaces pointwise and attainment reasoning with set-additive and
almost-everywhere reasoning:

| | axeyum | Mathlib |
|---|---|---|
| interval additivity | ~13 lanes: crossing index, clamping, uniform continuity | `Ioc a b ∪ Ioc b c ∪ Ioc c a = …` then `setIntegral_union` |
| why | the mesh is INTERVAL-RELATIVE, so two intervals' meshes do not align | sigma-additivity on disjoint sets is an AXIOM |

Their additivity is structural; ours is an approximation argument.
`CReal.riemannSum_split_exact` is the proof of that reading: additivity is
**exact, with no estimate at all**, precisely when the split point is a mesh
point. Measured, not asserted: **Mathlib has no Riemann integral at all** —
searching its tree finds Riemann zeta, Riemannian geometry, Riemann–Lebesgue
and Riemann mapping, no integration. Everything is Bochner.

## 2. Locatedness is the constructive analogue of measurability

Classically, *measurable* is the tameness hypothesis that makes the theory
work. Constructively that role is played by **located** — a set whose distance
function is computable. Bishop–Cheng constructive measure theory builds
integrable functions as the L1-completion of step functions and recovers
genuine limit theorems, constructively. So "how do we get structural additivity
and dominated convergence without classical logic" has an answer, and the
answer is the located/L1 theory rather than a cleverer Riemann argument.

This also sharpens a conflation this repository has been making. **EVT and LUB
are NOT the same failure**:

- **EVT**: the supremum VALUE of a uniformly continuous `f` on `[a,b]` is
  perfectly constructive (mesh maxima converge; `CReal.max` ships). What fails
  is the **argmax** — `CReal.evt_attained_max_decides_sign` shows an attaining
  point would decide the sign of an arbitrary real.
- **LUB for a general bounded set**: the VALUE itself is unavailable without
  **locatedness**. That is why this kernel ships Bishop completeness (every
  regular sequence of reals has a limit, constructed) instead.

`inf` is symmetric throughout, via `inf S = −sup(−S)`.

**Why the argmax specifically cannot exist**, in one line: computable functions
are continuous, `sup` is 1-Lipschitz in `f`, and `argmax` **jumps** — for
`f(t) = t·v` on `[0,1]` the argmax is `1` for `v>0` and `0` for `v<0`, so an
arbitrarily small perturbation moves the answer the full width of the interval.
No finite prefix of the input determines the output near the tie.

## 3. What to learn, and what NOT to conclude

1. **When a property ought to be structural, put it in the definition.**
   Additivity fought us because it was downstream of a mesh choice. Anything
   limit-shaped will keep fighting the same way — dominated convergence next,
   Fubini after that. The cheap fix is already identified in the architecture
   review §2 (a globally-anchored mesh makes additivity structural and moves
   the cost to boundary handling); the expensive fix is an L1 construction.
2. **Locatedness deserves to be first-class** if the sup/inf family is to work
   properly, rather than being reconstructed ad hoc per theorem.
3. **The trade is NOT free, and we should not present it as an upgrade.**
   Mathlib's integral buys structural additivity by surrendering computational
   content: it is `noncomputable` and returns a junk `0` off the integrable
   class. Ours runs. Bishop's constructive integration keeps the computational
   content but is a far heavier build. Choosing measure-theoretic foundations
   would trade this project's strongest property for the opponent's structural
   convenience — a real decision, to be made deliberately if at all.

## 4. The immediately actionable item

**`CReal.sup` does not exist and should.** For uniformly continuous `f` on a
compact interval it is constructive — mesh maxima converge, and `CReal.max`
with its lattice lemmas already ships. It is the honest **row 1** for the LUB
family, which is currently the only row 1 in the graded families that is an
absence rather than a theorem, and it is the located-sets lesson applied at the
cheapest available point.
