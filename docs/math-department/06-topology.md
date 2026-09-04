# 06 — Topology

Reviewer: a topologist — point-set and algebraic
Verdict, 2026-09-04: **nothing to review**
Last measured: 2026-09-04 at `1856cdb3c`

> "There is no topology here. Not a thin topology, not an unusual topology.
> Zero declarations. I am the shortest review in the department and the one
> that blocks the most people."

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

- [ ] **1. Choose the constructive topology and write the ADR.** Open sets,
      apartness spaces, or locales. Their view: this one decision is worth
      more than any five theorems, because it determines whether the analysis
      shelf ever generalizes.
- [ ] **2. A metric-space carrier with ℝ and `CPoint` as instances**, and
      completeness lifted from the existing `converges_of_cauchy`. The
      cheapest possible demonstration that the choice in (1) pays.
- [ ] **3. Bishop compactness — total boundedness plus completeness — on
      intervals**, then the extreme value theorem re-derived as an instance
      rather than re-proved.
- [ ] **4. Continuity as a topological notion**, with the existing
      `UniformlyContinuousOn` proved to imply it, so the two vocabularies are
      connected rather than parallel.
- [ ] **5. Products and subspaces**, which is where a topology carrier either
      composes or is revealed to be the wrong one.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero topology declarations, confirmed against a positive control. Three other reviewers blocked behind this file. | ledger snapshot at `1856cdb3c` |

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
