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

The fact ledger counts 2,758 propositions and cannot tell you that a
number theorist would be impressed and an algebraist would not. Coverage is
not uniform and it is not supposed to be, but "we have 2,487 proved facts"
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

| # | File | Field | Verdict, 2026-09-04 |
|---|---|---|---|
| 01 | [Number theory](01-number-theory.md) | elementary & analytic NT | **Impressed, with a ceiling.** A real first-year-graduate elementary library, stopping where the subject turns algebraic. |
| 02 | [Constructive analysis](02-constructive-analysis.md) | Bishop school | **Excited.** Among the most complete constructive real analyses anywhere; the FTC gap is the obvious next move. |
| 03 | [Classical analysis](03-classical-analysis.md) | measure, functional | **Weakened, not cleared, 2026-09-04.** The classical-axiom policy went against them (ADR-1601: hypotheses, not axioms) and a metric layer landed. Still no measure. |
| 04 | [Algebra](04-algebra.md) | groups, rings, fields | **Revised 2026-09-04.** The quotient question is decided by measurement and the first isomorphism theorem is proved over setoids. A thin shelf, no longer a blocked one. |
| 05 | [Geometry](05-geometry.md) | Euclidean, differential, algebraic | **Charmed, then bored.** Excellent classical plane geometry; nothing above it. |
| 06 | [Topology](06-topology.md) | point-set, algebraic | **Revised 2026-09-04.** A metric layer with 49 declarations landed and ADR-1602 settles the design: metric first, pointfree later, open sets never. Still no topological space. |
| 07 | [Combinatorics](07-combinatorics.md) | enumerative, extremal | **Week three, good foundations.** Finset and pigeonhole just landed; the carriers are right. |
| 08 | [Probability & statistics](08-probability-and-statistics.md) | finite & measure-theoretic | **Better than first reported.** ~30 proved theorems over ℚ, up to Chebyshev on sample means; everything above it waits on measure theory. |
| 09 | [Category theory](09-category-theory.md) | | **Absent, and philosophically opposed.** Concrete-carrier-first is the opposite of their method — but ℤ's universal property is already proved. |
| 10 | [Logic & foundations](10-logic-and-foundations.md) | proof theory, reverse math | **Most interested of anyone.** The kernel *is* the contribution, and the EM/LNP results are real reverse mathematics. |
| 11 | [Applied & computational](11-applied-and-computational.md) | formal methods, computable analysis | **Sees the most novel object here.** Proof-producing search into a small checker has little precedent. |
| 12 | [The chair](12-the-chair.md) | department head / referee | **Would sign the report.** Zero assumptions across 2,487 results and a rising machine-produced share. |
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

python3 scripts/validate-facts.py          # 2,758 facts, 0 errors as of 2026-09-04

# what a prelude actually proves (RELEASE ONLY -- debug SIGABRTs; lists
# theorems, NOT definitions, so pair every negative with a positive control
# of the same declaration kind)
cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory

# does a lemma already exist? search for the SHAPE, never the name, and
# rebuild first -- a stale binary reports a false ABSENT
cargo run --release -p axeyum-lean-kernel --example shape_search -- --const <C>
just brief <target>
```

Snapshot taken 2026-09-04, at `1856cdb3c`:

| area | proved | open | character |
|---|---|---|---|
| ℕ | 862 | 178 | number theory, deep |
| ℝ (constructed) | 476 | 0 | Bishop-style analysis |
| ℤ | 356 | 79 | modular arithmetic, reciprocity |
| ℚ | 330 | 0 | field, matrices, echelon, rank |
| ℂ (constructed) | 128 | 0 | algebraic, polynomials |
| plane geometry | 94 | 0 | coordinatized Euclidean |
| strings | 64 | 0 | formal languages |
| logic | 24 | 0 | intuitionistic; EM as hypothesis |
| lists | 17 | 0 | landed 2026-09-03 |
| solver fragments | ~50 | 0 | QF_BV, QF_FP, QF_LRA, QF_NIA, UF |

Totals: **2,487 proved, 262 open, 4 refuted, 3 conjectured, 2 computed.**
Every proved row carries an axiom footprint read from
`Kernel::axiom_footprint`, and the headline is that the footprint is empty.

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
