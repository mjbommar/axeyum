# 03 — Classical analysis

Reviewer: a classical analyst — measure theory, functional analysis, PDE
Verdict, 2026-09-04: **unmoved**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have a very careful Riemann integral. I have not used a Riemann
> integral since graduate school."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Works with Lebesgue integration, Banach and Hilbert spaces, and the
convergence theorems that make them usable. Reaches for dominated convergence
several times a week and for excluded middle without noticing. Regards
constructivity as an interesting philosophical position and a professional
handicap. Their test for a library is whether you can state and use "L² is
complete".

## What the library has today

Everything in [02-constructive-analysis.md](02-constructive-analysis.md), read
from this side of the aisle:

| what they want | what exists |
|---|---|
| Lebesgue integral | nothing; Riemann sums over an interval-relative mesh |
| measure, σ-algebra | nothing (the 117 grep hits for "measure" are all the word "measured" in comments) |
| dominated / monotone convergence | nothing |
| metric space | nothing; completeness proved for ℝ only, as `converges_of_cauchy` |
| topological space, open sets, compactness | nothing |
| normed space, Banach, Hilbert | nothing |
| Lᵖ spaces | nothing |
| Fourier analysis | nothing |
| distributions, Sobolev, PDE | nothing |
| complex analysis | `Complex` exists as a carrier with polynomials; no holomorphy, no contour integration |
| what does exist | IVT, EVT, uniform continuity on intervals, derivatives, Riemann integration, exp/cos/π/√ |

## Their verdict

Blunt: the analysis shelf stops in 1867. Riemann integration with explicit
moduli is a fine undergraduate development and it is not what modern analysis
is made of. Every technique they rely on — measure-zero exceptional sets,
almost-everywhere convergence, completeness of function spaces, compactness
arguments in infinite dimensions — is unavailable, and most of them are
unavailable *in principle* under the constructive commitment rather than
merely unbuilt.

Two specific objections they would raise, and both are fair:

**Constructive analysis makes the wrong theorems true.** They would point out
that the classical statements they use are often constructively false, not
merely unproved: a continuous function on a closed interval need not attain
its maximum constructively, and the library's EVT is therefore a different
theorem than the one they teach. That is not a defect of the library, but it
means a Mathlib-parity claim in analysis is not meaningful in this area
without saying which statement is meant.

**Measure theory is where the subject actually lives, and it needs classical
logic.** Constructive measure theory exists (Bishop has a chapter) and almost
nobody uses it. A library that wants classical analysts as users has to decide
whether to admit classical axioms in a labelled second tier.

Their one point of genuine interest: the library's habit of recording
[graded statement families](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
— constructive form, boundary refutation, decidable-fragment exact form,
labelled import — is exactly the right instrument for the disagreement above.
It lets the classical statement be present and labelled rather than absent or
silently substituted.

## What they would say is missing

Everything above. Ordered by what would change their assessment first:

- **A topology carrier.** Open sets, continuity in the topological sense,
  compactness. Nothing in classical analysis composes without it. See
  [06-topology.md](06-topology.md).
- **Measure and the Lebesgue integral**, with the three convergence theorems.
- **Normed and inner-product spaces**, with completeness, and ℝⁿ and ℓ² as
  instances.
- **Complex analysis.** Holomorphy, Cauchy's theorem, the residue calculus.
  This is also the gate on analytic number theory
  ([01-number-theory.md](01-number-theory.md)).
- **Multivariate calculus.** No ℝⁿ, no partial derivatives, no Fubini.

## The blocker

**A decision, not a construction.** Classical analysis needs excluded middle,
countable choice, and function extensionality, and the kernel has none of
them. The library's headline metric is that its axiom footprint is empty, and
importing this reviewer's subject means giving that up for the part of the
library that serves them.

The existing machinery for this is ADR-0603's graded families plus the axiom
footprint: a classically-proved theorem is admissible if the classical axiom
appears in its footprint and the ledger reports it, so the empty-footprint
count stays honest and separate. Nothing about that mechanism is built for
analysis yet, and `Nat.em_implies_lnp` / `lnp_unrestricted_implies_em` show the
kernel can already reason about EM as an explicit hypothesis rather than an
axiom — which may be the better route: *theorems conditional on EM*, keeping
the footprint empty.

That choice — classical axioms as footprint entries, versus classical
hypotheses discharged at use — is this reviewer's real question for the
project, and it is unresolved.

## Next five, in their priority order

- [ ] **1. Decide and document the classical-axiom policy.** Either EM as a
      labelled footprint entry, or EM as an explicit hypothesis in the
      statement. An ADR, not code. Everything else on this list depends on it.
- [ ] **2. A topological-space carrier**, even a minimal one, with ℝ as the
      first instance. Their view: the single structural piece whose absence
      blocks the most.
- [ ] **3. Metric and normed spaces, with completeness**, generalizing the
      existing `converges_of_cauchy` off ℝ.
- [ ] **4. Measure and the Lebesgue integral on ℝ**, with monotone and
      dominated convergence, stated in whichever regime (1) selects.
- [ ] **5. Complex analysis: holomorphy and Cauchy's integral theorem**, over
      the existing `Complex` carrier. Serves this reviewer and unblocks
      analytic number theory at the same time.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: no measure, no topology, no normed spaces, no complex analysis. Riemann integration and the interval theorems only. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed, and the answer is not the one this reviewer wanted** (roadmap W0-2, ADR-1601): classical principles stay **hypotheses**, never axioms. The measurement: carrying one costs 11 binders and 14 argument positions across ten theorems, and **zero obligations**, and does not grow with depth. Three findings decided it — the axiom option is at least three axioms (EM, countable choice and `funext`, which this file's blocker named together and nobody had priced), it devalues the certificates whose content is that a classical conclusion costs a decision principle, and it kills three passing gates. Items 2–5 are unaffected in substance; measure theory unblocks with a *stated shape* rather than with classical logic available by default. | `80aa8e52c` |
| 2026-09-04 | **Next Five item 4 opened, and not in the shape this reviewer asked for** (roadmap W3-1, ADR-1612). Measure theory arrives integral-first: a predicative pre-integration space with the interval integral, finite sums and a Dirac space as instances, measure *derived* as the integral of an integrable indicator, and monotone convergence as a graded family whose classical member carries a decision principle on one binder. No σ-algebra, no Lebesgue integral as a primitive, and dominated convergence not yet stated. The lane says plainly that this reviewer may reasonably say an integration space is not their subject. The honest count: 70 declarations, 1 of 6 interval theorems re-derived generically — the rest *are* the space's axioms — and L¹ as a completion blocked on `Sigma`'s absence. | `3d5320f68` |

## How to re-measure

```sh
for t in measure lebesgue sigma_algebra topology compact metric_space \
         banach hilbert holomorphic contour_integral fubini; do
  printf '%-20s %s\n' "$t" "$(grep -rli "$t" crates/axeyum-lean-kernel/src/ | wc -l)"
done
# positive control: riemann returns 16 files, so a zero above is a real zero
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — the same shelf,
  judged favourably
- [06-topology.md](06-topology.md) — the prerequisite
- [08-probability-and-statistics.md](08-probability-and-statistics.md) —
  blocked behind measure theory
- [ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
