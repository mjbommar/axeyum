# 05 — The mathematics DAG: what exists, what is missing, what to research now

**The reframe.** "Build the complete DAG of all mathematics within axeyum"
sounds like a construction project. It is not. **The DAG already exists**, next
door, and has for months. What is missing is the *annotation* that connects it
to what axeyum can decide, certify and prove.

This is also the largest body of work available that does **not** touch
`crates/axeyum-lean-kernel/`, and is therefore fully parallelisable against the
lane that owns it (see
[`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md)).

## What we already have — measured

`../math-education/graph/`:

```
1,567 concepts        1,536 of them carrying prerequisite edges (98%)
2,254 prerequisite edges
   19 longest prerequisite chain   (deepest node: C:optimisation-calculus)
  154 roots (depth 0)
```

Thirteen strands, which is a *pedagogical* partition of mathematics:

| strand | concepts | | strand | concepts |
|---|---:|---|---|---:|
| probability-and-data | 235 | | discrete | 128 |
| logic-and-proof | 205 | | fractions-and-ratio | 127 |
| algebra | 184 | | infinity-and-analysis | 91 |
| geometry | 180 | | arithmetic-structure | 81 |
| number | 152 | | counting-and-quantity | 34 |
| computation | 147 | | practice / data | 3 |

And — the part nobody has used — every concept carries an **epistemic status**:

```
axiom     586      proved     551      empirical  257
computed  155      open        14      conjectured  4
```

Plus 148 misconceptions, 42 techniques, 88 people, 61 works, over an RDF/OWL/SKOS
ontology with `Concept`, `Encounter`, `Misconception`, `Bridge`, `Lesson`,
`BloomLevel`, `EpistemicStatus`, `DomainArea` and more.

**So the DAG is not the gap.** A 1,567-node prerequisite DAG of depth 19, with
epistemic annotations, already exists. axeyum's curriculum — the thing that maps
it to decidable fragments — has **23 nodes**. That ratio, 23 : 1,567, is the
actual gap.

## The prior art, which we should read before building anything

This exact problem has been studied, recently, with downloadable data.

- **"The Network Structure of Mathlib"** (arXiv:2604.24797, 2026) — a multilayer
  graph of **308,129 declarations, 8.4 million edges, 7,563 modules**. Three
  findings bear directly on us:
  - **human taxonomies diverge from logical structure** — 50.9% coupling across
    namespaces. Our 13 strands are a human taxonomy; the logical DAG will not
    agree with them, and that disagreement is information rather than error.
  - developers use a **median 1.6% of imported scope** — an argument that
    "import the world" is not how a library gets used.
  - formalisation **compresses semantic hierarchies**, and network centrality
    tracks language infrastructure rather than mathematical importance.
- **Mathlib4 Theorem Dependency Graph** (LeanDojo Benchmark 4, v10, on Mendeley)
  — a directed theorem-dependency graph, downloadable. This is a *formal* DAG we
  can align our *informal* one against.
- **TheoremGraph: Bridging Formal and Informal Mathematics** (arXiv:2606.25363)
  — literally the mapping problem below. Read before designing our own.
- **KnowTeX: Visualizing Mathematical Dependencies** (arXiv:2601.15294).

The scale context is worth stating plainly: Mathlib is **308,129 declarations**;
`nat_prelude` is **139 proved theorems** (re-measured 2026-08-19 with
`--example nat_theorem_inventory`; 106 when this was written). That is a factor
of roughly 3,000. The useful response to that is not to race — it is to be
precise about which *fragment* of the DAG we can carry evidence for, which
nobody else measures.

## The research programme — all of it parallelisable

### D1 — Annotate the existing DAG with fragment and decidability

The curriculum's 23 nodes each carry `decidability`, `axeyum_theory` and the
`axeyum-scenarios` family that exercises them. **Extend that annotation across
the 1,567.** Not by hand: propose from strand + concept shape, then verify a
sample, and record the confidence.

The output is the first honest answer to "what mathematics can axeyum reach",
and it is a *measurement*, not a plan.

### D2 — Compute the reachability frontier over the DAG

With D1's annotation and 2,254 edges, this becomes a graph computation:

- **reachable now** — every prerequisite decidable in a fragment we have;
- **one capability away** — reachable if exactly one missing fragment lands.
  That set, ranked by size, is a **feature request written by the mathematics
  itself**;
- **beyond the horizon** — and *why*, which is more useful than the fact.

The corpus audit already produced a small version of this by hand: of 148
misconceptions, **85 formalisable and refutable, 16 out of fragment (each naming
the fragment it needs), 46 not checkable propositions**. Those 16 are the
prototype of D2's middle tier.

(Those were 86 / 17 / 44 here until 2026-08-17, quoted from an audit whose
census file was never committed. Re-derived and now committed as
[`artifacts/reachability/r3-census.tsv`](../../artifacts/reachability/r3-census.tsv):
one of the 17 was a *distractor form* counted as a corpus row and one genuine
out-of-fragment row was missing. The same measurement extends the census to the
graph's 42 `techniques`, where 19 more rows are out of fragment and 16 of those
want one thing — induction over ℕ as a discharged schema. See R3 in
[`04`](04-reachability.md).)

### D3 — Align our informal DAG against Mathlib's formal one

Download the LeanDojo dependency graph and ask: how many of our 1,567 concepts
have a Mathlib counterpart, and does Mathlib's *logical* order agree with our
*pedagogical* order? The Network Structure paper predicts it will not — 50.9%
coupling across namespaces — and the disagreements are exactly where a
pedagogical DAG teaches something a formal one does not, or vice versa.

This also gives the library track a **construction order validated against a
library that exists**, rather than one we reasoned out ourselves — though as of
2026-08-19 the order was walked first (ℤ, ℚ, ℝ, ℂ, all constructed) and D3's
job changed with it; see "What to do first" below.

### D4 — Use `epistemic_status` as the evidence work queue

**551 `proved` + 155 `computed` = 706 concepts whose status is a mathematical
claim.** Each is a candidate for axeyum evidence: a scenario family, a
negative control, or a certificate. That is a work queue two orders of magnitude
larger than the 23-node curriculum and it already exists.

The **14 `open` and 4 `conjectured`** are the horizon markers, and they are
honest ones — Collatz, Goldbach, twin primes, the continuum hypothesis,
travelling salesman, packing. Nothing in axeyum's reach. Their value is that a
DAG which labels its own open problems can never quietly claim to have covered
mathematics.

### D5 — Close the ledger ↔ graph loop

The claim ledger already carries **435 concept references, all now resolved and
pinned** to a `math-education` commit. So the wiring exists in one direction:
a claim knows which concepts it is about. The reverse — *which concepts have
axeyum evidence* — is a join nobody has run. Run it, and publish it as coverage.

### D6 — Fix what D1 will otherwise inherit

Three defects the corpus audit found, all in the graph and none ours to correct
unilaterally:

- a distractor whose **conclusion is true** (`3/4 > 1/2`, wrong reasoning) —
  anything consuming `distractor_forms` as false statements will mark a correct
  answer wrong;
- `"3.4 is even"` is **ill-typed, not false**;
- **ten live near-duplicate pairs**, two sharing an identical distractor string.

These matter more once the graph is consumed mechanically than they did when it
was read by people.

## What to do first

1. **D4 then D1** — the epistemic labels already partition 706 concepts into a
   work queue; annotating outward from those is cheaper than annotating all
   1,567 cold.
2. **D3's download and comparison** — cheap, external, and it validates or
   refutes the construction order in [`02`](02-the-library.md).

   > **Reordered 2026-08-19.** This item was placed second because it was meant
   > to be read *before* anyone spent months on ℚ and ℝ. Both were built first —
   > ℚ on 2026-08-16, ℝ (ADR-0512) and ℂ (ADR-0521) by 2026-08-19 — and neither
   > took months, so D3's value has changed rather than lapsed. It is no longer
   > a *check on a plan*; it is now a **coverage measurement against a library
   > that exists**: which of Mathlib's ℝ/ℂ development our 94 `CReal` + 39
   > `Complex` declarations cover, and — the useful direction — which of its
   > constructions are unavailable to us at all, since ours is a constructive
   > setoid with no `Quot.sound`, no `propext` and no `funext`. That is a
   > comparison nobody else can run on their own library, and it moves D3 from a
   > pre-flight check to a standing metric. It stays second for the same reason:
   > cheap, external, and it constrains what comes after.
3. **D2 once D1 has a first pass** — the "one capability away" set is the
   highest-value output of this entire strand, because it converts a roadmap
   from opinion into a ranked consequence of the mathematics.

None of this touches `crates/axeyum-lean-kernel/`. All of it can run while the
library lane builds ℤ.
