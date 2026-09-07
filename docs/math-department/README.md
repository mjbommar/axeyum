# The math department review board

Twelve standing reviewers, one file each. Every file records **what the
library measurably has today** in that field, **how that field's practitioners
would judge it**, and **the next five things they would want**, with a
progress log so the judgement can be re-run and compared rather than
re-remembered.

This is a *review* instrument, not a plan. The queue of work lives in
[PLAN.md](../../PLAN.md) and the per-lane status files; the teaching order
lives in [the curriculum graph](../curriculum/README.md); the strategic
argument lives in [the formalized-math strand](../formalized-math-2026-08/README.md).
What this folder adds is an outside view: for each mathematical culture, what
would they say if they read our ledger, and what would change their mind.

## Why personas

The fact ledger counts 2,963 propositions and cannot tell you that a
number theorist would be impressed and an algebraist would not. Coverage is
not uniform and it is not supposed to be, but "we have 2,687 proved facts"
hides which fields those facts would matter to. A persona forces the
question a metric cannot ask: *who is this good enough for, and why not for
everyone else?*

Each reviewer is written as an informed, unsentimental practitioner in that
field who has just read the ledger and the kernel's axiom footprints. They
are allowed to be harsh. A file whose verdict is entirely favourable is
probably not doing its job.

**Start with [the roadmap](00-roadmap.md)** if you want the synthesis: the
sixty Next Five items across all twelve files, collapsed to 51 distinct items
in four waves, with the seven convergence points where independent reviewers
asked for the same thing, a status board, and a history log.

## The reviewers

| # | File | Field | Verdict (re-measured 2026-09-06 unless dated otherwise) |
|---|---|---|---|
| 01 | [Number theory](01-number-theory.md) | elementary & analytic NT | **Impressed; the shelf grew, the ceiling did not move (2026-09-06).** 1,291 proved ℕ/ℤ facts; Fermat's two squares, the prime-counting shelf and the arithmetic-function family landed; no bound on π(x) of any kind, and Chebyshev is blocked by a held-out family, not by analysis. |
| 02 | [Constructive analysis](02-constructive-analysis.md) | Bishop school | **Excited, and for a different reason than two days ago (2026-09-06).** The subject moved off the line: 629 `CReal` declarations, the metric layer, Bishop compactness, ℝⁿ, L¹; only three completeness theorems exist and there is no completion. |
| 03 | [Classical analysis](03-classical-analysis.md) | measure, functional | **Moved, and one complete function space short of interested (2026-09-06).** Seven of the file's "nothing" rows were false; measure is derived from the integral, holomorphy reaches the power rule; no completion, no dominated convergence, no Cauchy–Riemann equations. |
| 04 | [Algebra](04-algebra.md) | groups, rings, fields | **The spine grew a shelf, and there is still not one ideal (2026-09-06).** 130 generic theorems on the two spines; quotient groups, the first isomorphism theorem in both forms, polynomial rings, modules, constructive fields and vector spaces; `ideal` occurs zero times in the kernel; invariance of dimension is a theorem about tight fields. |
| 05 | [Geometry](05-geometry.md) | Euclidean, differential, algebraic | **Upgraded; one seat of three is now satisfied (2026-09-06).** Angles, isometries, conics, incidence with two models and Playfair all landed (`Geo` 164); affine incidence geometry, not Euclidean (no betweenness, no congruence); five committed geometry certificates carry no fact. |
| 06 | [Topology](06-topology.md) | point-set, algebraic | **The shelf exists (2026-09-06).** `Metric` 97 and `Top` 53 declarations, all axiom-free; the frame is pointfree; no Hausdorff, no connectedness; the twelve product-metric declarations are invisible to the retrieval index. |
| 07 | [Combinatorics](07-combinatorics.md) | enumerative, extremal | **A real first course, with the two shelves joined at two points (2026-09-06).** Schur's number and R(3,3) as theorems, Hall's marriage theorem, inclusion–exclusion, Vandermonde and the binomial theorem over ℕ (both wrongly recorded absent); no walks, paths or trees, no Ramsey theorem in general. |
| 08 | [Probability & statistics](08-probability-and-statistics.md) | finite & measure-theoretic | **The finite shelf builds its own distributions and beats Chebyshev's rate (2026-09-06).** 74 axiom-free declarations; measure exists and unlocked nothing; the missing object is a product space, not a measure. |
| 09 | [Category theory](09-category-theory.md) |  | **The subject exists now (2026-09-06).** 107 `CatS` declarations, nine proved facts, footprint 0, the category of groups with products; the uniqueness theorems cannot yet be applied to the large-level instances, and every small-level universal-property instance is a vacuous control. |
| 10 | [Logic & foundations](10-logic-and-foundations.md) | proof theory, reverse math | **Still the most interested reviewer, and now the one whose shelf moved the most (2026-09-06).** 141 first-order declarations: soundness, Robinson's Q with order, its model and consistency, Gödel numbering with the decode round trip; compactness and proof theory proper absent; the general retrieval tools are blind to all of it. |
| 11 | [Applied & computational](11-applied-and-computational.md) | formal methods, computable analysis | **Sees the most novel object in the building (2026-09-06).** Six producers, a 472-test producer sweep, the CAS at 155k lines with a 73.8% cas-internal residue and 1,019 uncertified public functions; the enclosure layer has zero ledger facts; the sum-of-squares reconstruction fallback mints axioms under the same theorem name as the honest route. |
| 12 | [The chair](12-the-chair.md) | department head / referee | **Would sign the report, and would strike three sentences (2026-09-06).** 2,584 of 2,687 proved facts axiom-free, all on one route, so the axiom-free headline needs rewording; the retirement count has been flat for three days while two hundred facts landed, so the production-rate claim is retired; and the coverage claim stays struck. The department-wide finding is now that the retrieval index builds 15 of the kernel's 31 preludes and the ledger names 599 of 3,319 theorems nowhere, so two blind spots look like success. |
| 13 | [The CAS, as a tool](13-computer-algebra.md) | all twelve, asked about `axeyum-cas` | **Deep calculus, overflows at 128 bits.** Every chair outside calculus and elementary number theory finds nothing to reach for; the Next Ten are compute capability, not bridges. |
| 14 | [The Lean language, as a boundary](14-lean-lang.md) | all twelve, asked what "Lean compatible" would have to mean | **Agrees with Lean's kernel on everything asked; reachable from Lean by nobody.** Two pins, three red gates since 2026-09-03; the Next Ten start with green gates and end with saying what the claim is. |

## The shared snapshot

Every file's "measured today" section is a view of one inventory. Re-measure
before editing any of them, and record the date.

```sh
# facts by fragment and status (the ledger view every persona file quotes)
python3 - <<'PY'
import json, glob, collections
frag, stat = collections.Counter(), collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f))
    frag[(d.get('formal') or {}).get('fragment', '?')] += 1
    stat[d.get('epistemic_status', '?')] += 1
print(sum(frag.values()), 'facts'); print(frag.most_common()); print(stat)
PY

python3 scripts/validate-facts.py          # 2,963 facts, 0 errors as of 2026-09-06

# what a prelude actually proves (RELEASE ONLY -- debug SIGABRTs; lists
# theorems, NOT definitions, so pair every negative with a positive control
# of the same declaration kind)
cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory

# does a lemma already exist? search for the SHAPE, never the name, and
# rebuild first -- a stale binary reports a false ABSENT
cargo run --release -p axeyum-lean-kernel --example shape_search -- --const <C>
just brief <target>
```

Snapshot taken 2026-09-06, at `9f2489a1f` (the 2026-09-04 snapshot at
`1856cdb3c` read 2,487 proved / 262 open; the method is the fragment count
in the block above):

| area | proved | open | character |
|---|---|---|---|
| ℕ | 918 | 182 | number theory, deep; Hall, inclusion–exclusion, prime counting |
| ℝ (constructed) | 485 | 0 | Bishop-style analysis, power series with a radius |
| ℤ | 375 | 80 | modular arithmetic, reciprocity, Fermat's two squares |
| ℚ | 333 | 0 | field, matrices, echelon, rank, finite probability |
| ℂ (constructed) | 162 | 0 | algebraic, polynomials, holomorphy to the power rule |
| plane geometry | 101 | 0 | coordinatized; incidence and affine models beside it |
| strings | 64 | 0 | formal languages |
| propositions on structures | 30 | 0 | setoid algebra, categories, first-order logic |
| logic | 24 | 0 | intuitionistic; EM as hypothesis |
| lists | 17 | 0 | landed 2026-09-03 |
| metric / integration | 9 + 5 | 0 | metric layer, L¹, monotone convergence on a hypothesis |
| solver and CAS fragments | ~60 | 0 | QF_BV, QF_FP, QF_LRA, NRA, UF, hypergeometric summation |

Totals: **2,687 proved, 267 open, 4 refuted, 3 conjectured, 2 computed.**
Every proved row carries an `axiom_footprint` read from
`Kernel::axiom_footprint`. The headline, stated precisely (ADR-1674): 2,584 of the 2,687 proved facts carry an empty `axiom_footprint`, all of
them on the `kernel-lean` route — the only route that can make the claim, since
`validate-facts.py` rejects an empty footprint on the other five. Of the 103
remaining, 101 are on those five routes and 2 are `kernel-lean` exceptions.

## The constraint that shapes almost every verdict

The kernel admits Lean's four-declaration quotient package (`Quot`,
`Quot.mk`, `Quot.lift`, `Quot.ind`) but **not `Quot.sound`**, and has no
`funext`, no `propext`, and no choice. You can form a quotient type and lift a
function out of it; you cannot prove that two related representatives are
equal. Six of the twelve verdicts below trace back to that one fact. It is
why ℝ is a Bishop setoid
([ADR-0512](../research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)),
why the algebra spine had to be built twice (`Alg` over `Eq`, `AlgS` over an
explicit equivalence), and why abstract algebra has not started.

Whether to add `Quot.sound` is therefore the single largest open question in
the library's direction, and it is a trade, not an oversight: one axiom in
every downstream footprint, against the whole of quotient-based algebra. See
[04-algebra.md](04-algebra.md) § The blocker for the argument on both sides.

## How to keep these files honest

- **Re-measure before you edit.** Every number in a persona file names the
  command that produced it. If you cannot re-run it, delete the number.
- **Log the change.** Each file ends with a progress table; append a row
  rather than rewriting the verdict silently, so the trajectory is readable.
- **Do not let a verdict drift up without evidence.** A field's verdict
  improves when a named item from its Next Five lands and the fact ledger
  shows it, not when the prose gets warmer.
- **A persona may be wrong.** These are projections, written by an assistant
  reading the ledger, not solicited from practitioners. Where a real
  mathematician in that field disagrees, their view supersedes the file and
  the file records that it was corrected.
- **Search for the shape, not the name.** The first pass of
  [08](08-probability-and-statistics.md) reported the probability shelf as a
  single theorem, because it searched for Mathlib's `probability_space` and
  `random_variable` rather than for expectation and variance. The real count is
  about thirty. Every "absent" in these files must be paired with a positive
  control on the same method, and the control must postdate the change being
  asked about. See
  [finding existing lemmas](../contributor-guide/finding-existing-lemmas.md).
- **The Next Five are a wish list, not the queue.** They become work when a
  lane brief cites them and PLAN.md carries the task.
