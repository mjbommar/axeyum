# 06 — Topology

Reviewer: a topologist — point-set and algebraic
Verdict, 2026-09-04 (revised same day): **there is now something to review — a metric layer with 49 declarations — and the design question is settled**
Last measured: 2026-09-04 at `1856cdb3c`

> "There is no topology here. Not a thin topology, not an unusual topology.
> Zero declarations. I am the shortest review in the department and the one
> that blocks the most people."
>
> **Revised the same day:** "You built the metric layer instead of asking me
> which topology to build, and the answer fell out: nothing in your record is
> a subset, so my objection to membership predicates never applied. I withdraw
> the blocking status. I still have no topological space."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Thinks in open sets, continuity as preimages, compactness, and connectedness,
then in fundamental groups, homology, and covering spaces. Regards topology
less as a subject than as the language every other analytic and geometric
subject is written in. Their test is whether you can say "f is continuous"
without mentioning ε.

## What the library has today

**Nothing.** Measured, not estimated:

| searched | files |
|---|---|
| `topology` | 0 |
| `open_set` | 0 |
| `compact_space` | 0 |
| `metric_space` | 0 |
| connectedness, homotopy, homology, fundamental group | 0 |

Positive control on the same method: `riemann` returns 16 files, `wilson`
returns 38, so these zeros are real zeros and not a search artifact.

What exists that a topologist would recognize as *adjacent*, all of it
ε-δ-and-modulus rather than open-set:

- `CReal.UniformlyContinuousOn` — continuity on an interval, defined with an
  explicit modulus
- `CReal.converges_of_cauchy` and the limit apparatus — completeness of ℝ,
  proved for ℝ specifically and not as an instance of anything
- `CReal.supOn`, `lubSet` — the least-upper-bound property on intervals
- the intermediate and extreme value theorems, proved by bisection on
  intervals rather than by connectedness or compactness arguments
- `CPoint` with `distSq` — a plane with a distance, and no notion of a
  neighbourhood

So the library has several theorems that are *classically* topological
statements, each proved by hand on the specific carrier, with no shared
vocabulary between them.

## Their verdict

The review is short and the consequence is long. Every proof in this library
that would be a topological argument elsewhere has been done concretely and
locally: bisection instead of connectedness, explicit moduli instead of
compactness, per-carrier completeness instead of a complete metric space. That
is a legitimate way to build a constructive analysis library — Bishop does
much the same — and it means **nothing generalizes**. The IVT is a theorem
about `CReal` on an interval. It is not an instance of anything, so proving it
again for `CPoint`, or for a function space, would be starting over.

The topologist's specific point, which the department should hear: their
absence is not one gap among twelve. It is the shared prerequisite for
[03-classical-analysis.md](03-classical-analysis.md) (which needs open sets
before measure), for [08-probability-and-statistics.md](08-probability-and-statistics.md)
(behind measure), and for the differential half of
[05-geometry.md](05-geometry.md) (manifolds are locally-Euclidean topological
spaces). **Three of the twelve reviewers are blocked behind this file**, which
makes the emptiest shelf in the library also the highest-leverage one.

They would add one constructive caveat, in fairness: point-set topology is
awkward constructively. Open sets defined by membership predicates behave
badly without excluded middle, and the constructive tradition prefers *located*
subsets, *apartness spaces*, or formal/pointfree topology (locales) precisely
because the classical definitions do not transfer. So the right first move
here is a design decision, not a transcription of a textbook chapter.

## What they would say is missing

Everything, in the order a course would build it:

- **A space carrier.** Whatever the design decision selects: topological
  spaces by open sets, apartness spaces, or locales.
- **Continuity as a topological notion**, with the existing
  `UniformlyContinuousOn` shown to imply it on ℝ.
- **Metric spaces**, with ℝ and `CPoint` as instances, and completeness
  generalized off `CReal.converges_of_cauchy`.
- **Compactness** in a constructively usable form — total boundedness plus
  completeness, per Bishop, rather than open covers.
- **Connectedness**, and the IVT re-derived as an instance rather than
  re-proved.
- **Product and subspace constructions**, without which nothing composes.
- **Algebraic topology.** Fundamental group, homology. Far away; needs group
  quotients, hence [04-algebra.md](04-algebra.md).

## The blocker

**A design decision, then ordinary work.** No kernel primitive is missing for
point-set topology in the constructive style: a space can be a structure over
a carrier with membership predicates, exactly like the `Alg` spine. What is
missing is the choice of *which* constructive topology to build, and that
choice determines whether the existing analysis theorems become instances or
stay orphans.

Two secondary constraints:

- **No `funext`.** Continuous maps as elements of a set, and function spaces
  with their own topology, need either function extensionality or a setoid
  discipline for maps — the same fork as
  [04-algebra.md](04-algebra.md).
- **Algebraic topology needs quotients.** The fundamental group is a quotient
  of loops by homotopy. That half of the subject is behind the same gate as
  abstract algebra.

## Next five, in their priority order

- [x] **1. Choose the constructive topology and write the ADR.** *Done 2026-09-04, ADR-1602: metric first, pointfree later, open sets never.* Original framing: Open sets,
      apartness spaces, or locales. Their view: this one decision is worth
      more than any five theorems, because it determines whether the analysis
      shelf ever generalizes.
- [x] **2. A metric-space carrier with ℝ and `CPoint` as instances**, and
      completeness lifted from the existing `converges_of_cauchy`. *Done
      2026-09-04: 49 declarations, empty footprints, and completeness did
      generalize — at a cost of two bridge lemmas that already existed. The
      obstruction was never topological: the convergence predicates are
      phrased on rational samples rather than on the absolute value.*
- [x] **3. Bishop compactness — total boundedness plus completeness — on
      intervals** — *done 2026-09-04, EVT re-derived as the same term.*, then the extreme value theorem re-derived as an instance
      rather than re-proved.
- [x] **4. Continuity as a topological notion** — *done 2026-09-04, the bridge is definitional.*, with the existing
      `UniformlyContinuousOn` proved to imply it, so the two vocabularies are
      connected rather than parallel.
- [ ] **5. Products and subspaces** — **[ADR-1602] split this item.** The
      product is buildable today. The subspace is blocked on `Subtype`, which
      is absent from the kernel, so the right move is to relativize rather
      than carve.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero topology declarations, confirmed against a positive control. Three other reviewers blocked behind this file. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1 and 2 both landed** (roadmap W0-3 and W2-1). The design question is answered by ADR-1602 — metric layer first, pointfree frames for topology proper when needed, open-set spaces never — and it was answered by *building* rather than deciding. 49 `Metric` declarations, all footprint 0, with ℝ and the Euclidean plane as instances and completeness generalized off ℝ. Two things the build taught that no argument would have: **nothing in the record is a subset**, so this reviewer's objection to membership predicates never arose; and the plane's **unsquared** triangle inequality landed on the first kernel run, **refuting `CPointPrelude::cauchy_schwarz`'s own doc comment** that the statement 'is not expressible, let alone provable, here' — a stale blocker predating `CReal.sqrt`. | `b7df58b7b`; `metric::` 17 passed |
| 2026-09-04 | **Next Five items 3 and 4 landed** (roadmap W2-3, W2-2), and both were the cases that could have refuted ADR-1602. Continuity over an arbitrary pair of metric spaces, with the `CReal` bridge costing **zero estimates** because the metric distance reduces to `abs (x + -y)` and `UniformlyContinuousOn`'s modulus was already in the right shape — the two predicates are definitionally the same proposition. Bishop compactness as total boundedness plus completeness, no covers; the EVT proved over any totally bounded subset of any metric space with completeness never used, and **the interval EVT re-derived from it as the same interned term** that the direct proof produces. 44 declarations, 43 admitted first time. The reviewer's item 5 (products and subspaces) remains split: products buildable, subspaces on `Subtype`. | `5bb30b809`; `metric::` 29 passed |

## How to re-measure

```sh
for t in topology open_set compact metric_space connected homotopy homology \
         fundamental_group locale apartness_space; do
  printf '%-20s %s\n' "$t" "$(grep -rli "$t" crates/axeyum-lean-kernel/src/ | wc -l)"
done
# positive control on the same method -- if this is not 16, the search is broken
printf '%-20s %s\n' riemann "$(grep -rli riemann crates/axeyum-lean-kernel/src/ | wc -l)"
```

## Related

- [03-classical-analysis.md](03-classical-analysis.md),
  [08-probability-and-statistics.md](08-probability-and-statistics.md),
  [05-geometry.md](05-geometry.md) — the three reviewers blocked behind this
  one
- [02-constructive-analysis.md](02-constructive-analysis.md) — the theorems
  that would become instances
