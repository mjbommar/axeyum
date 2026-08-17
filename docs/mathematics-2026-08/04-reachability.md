# 04 — What this stack cannot yet state

The first three documents ask what we can decide, certify and prove. This one
asks the prior question: **what mathematics can axeyum express at all?**

The project already has a map for this and does not use it as one. The
curriculum is a machine-readable prerequisite DAG in which every node carries a
decidability class, the axeyum theory it maps to, and the `axeyum-scenarios`
family that executes it. Its invariants are test-validated: every prerequisite
id exists, the graph is acyclic, `unlocks` is the exact inverse of
`prerequisites`.

## The map, measured

```
23 nodes
decidability:  bounded 16 · computable 6 · decidable 1
status:        covered 19 · lean-horizon 4
family:        4 of 23 nodes name no executing scenario
```

Three things follow immediately.

**The stack is overwhelmingly a *bounded* reasoner.** 16 of 23 nodes are
`bounded` — decided only for finite or fixed instances. Exactly one node is
`decidable` in the full sense. That is the honest characterisation of what
axeyum is today, and it matches what the campaign produced: finite colouring
problems over `BitVec`-shaped domains, decided exhaustively.

**19 of 23 are marked `covered` while 4 name no executing family.** `covered` is
a *stored* status, not a re-derived one — the same defect class the engineering
strand documents, reaching the routing table for the whole vision. The corpus
audit confirmed it concretely: `divisibility-and-euclid` claimed
`computable`/`covered` with **zero** negative-control evidence until it was
closed by hand, and `reals` is `covered` while our fragment cannot support the
claim.

**The number systems are the worst-evidenced nodes.** `integers` and `rationals`
are both `computable`/`covered`; `reals` is `bounded`/`covered`. Meanwhile
`int_prelude` is **0 proved / 3 assumed** and `axeyum-scenarios` `unreachable!()`s
on `Sort::Int` and `Sort::Real`, so **no negative control about them is even
expressible**. Three nodes assert coverage of the sorts the stack can neither
prove about nor produce evidence about.

## The 23-node map against the 1,567-concept graph

The sibling `math-education` repository carries **1,567 concepts**, 148
misconceptions, 88 people, 61 works and 42 techniques, over an RDF/OWL/SKOS
ontology with content authored in YAML and projected into the vocabulary.

The curriculum is the **routing table** that should connect that content to
axeyum's decidable fragments. It has 23 entries against 1,567 concepts — a ratio
of roughly 1:68. The claim ledger already references the graph (435 concept
refs, now all resolved and pinned), so the wiring exists; the routing table is
simply almost empty.

That is not an argument for 1,567 curriculum nodes. It is an argument that
**nobody has asked, systematically, which mathematics this stack can reach** —
and the corpus audit is the only time anyone had, until R3 below re-ran it: of
148 misconceptions, **85 (57.8%) are formalisable and refutable, 16 are out of
fragment, 46 are not checkable propositions at all** (the audit reported
86 / 17 / 44; see R3 for the four rows that moved and why). That is the first
honest reachability measurement the project has, and its author flagged the
caveat that a *school*-mathematics corpus overlaps our fragments by
construction, so 57.8% measures that corpus rather than "real mathematical
error".

## What to do

**R1 — Re-derive `covered` from evidence.** A node keeps the label only if it
names a family that runs. This is cheap and it converts the map from assertion
to measurement.

**Done 2026-08-16, and it strips nothing.** `scripts/check-curriculum-coverage.py`
now derives the flag from the source tree on every `just foundational-resources`
run, on two conditions: the node's example packs are pulled into an executing
`math_resource_*_routes.rs` suite, and at least one of those instances
participates in a refutation assertion. Measured: **19 covered / 19 running /
19 with a negative control.** No node loses the label.

Two corrections to the paragraph above, both from measuring rather than reading:

- *"Four nodes name none today; three of those are the number systems"* is not
  what the map says. The four naming no family are exactly the four
  `lean-horizon` nodes — `cardinality`, `complex`, `sequences_and_limits`,
  `calculus` — which are the ones explicitly not claiming coverage. All 19
  `covered` nodes name a family, and every one of those families runs.
- The `int_prelude` premise below is stale: ℤ was proved out on 2026-08-16
  (`Int.euclidean_decomposition` became a theorem; the integer prelude is
  **0 axioms**, not 3), and ℚ now exists as a normalised structure over it. R4's
  "every node above ℕ is unevidenceable in principle" no longer holds for ℤ.

Condition 2 currently has no discriminating power, and the honest reason is a
fact about the tree, not a weakness in the check: all five resource suites carry
**zero** sat-assertion markers against 34 refutation markers — they are
refutation suites by construction. The controls in
`scripts/tests/test_check_curriculum_coverage.py` keep that from decaying into a
condition that cannot fail: a synthetic sat-only route is correctly reported as
uncontrolled, and deleting either condition kills exactly one test.

What the measurement *did* surface: two packs on disk —
`finite-integration-v0` and `real-analysis-rational-v0` — are validated
structurally and executed by no suite at all. They belong to no `covered` node,
so the gate stays green, but they are the honest edge of the map.

**R2 — Make `bounded` say what it is bounded *by*.** Sixteen nodes share one
word covering very different situations: bounded by bit width, by enumeration
domain, by an admission cap like `MAX_CROSS_PRODUCTS`, or by a resource budget.
Those have different fixes and different frontiers, and collapsing them hides
exactly where the ceiling is.

**Done 2026-08-16.** The information already existed — `axeyum_fragments` names
the fragment each node runs in — but as free prose, one signature per node, so
it never aggregated and could not be compared. `check-curriculum-coverage.py`
now derives a closed vocabulary from it:

| bound | nodes |
|---|---:|
| bit-width | 9 |
| arithmetic-resource-budget | 7 |
| enumeration-domain | 6 |
| real-algebraic-admission-cap | 4 |
| *unclassified* | 1 |

Deliberately a **set**, not one label: `BV / enumeration (finite groups)` is
bounded by a bit width *and* by an enumeration domain, and picking one would be
a fiction. The counts therefore exceed 16.

The single unclassified node is `proof_methods`, whose fragment is "Refutation
(negate-and-decide)" — a strategy, not a ceiling. That is left honest rather
than forced into a bucket, and pinned by a ratchet: the unclassified count may
not grow. That is the mechanism, because one word covering four situations is
exactly what happens when nothing objects to the second.

**R3 — Run the reachability census beyond the school corpus.** The misconception
audit is a good instrument used once on an easy corpus. Point it at something
adversarial — the graph's `techniques`, or the `B` (out-of-fragment) rows, which
already *name the fragment each would need*. Those rows are a ranked feature
request written by the mathematics itself.

**Done 2026-08-17, and the 17 does not survive re-derivation.** Measured against
the sibling `math-education` graph at commit `ce3e2a5` — 148 misconception files
and 42 technique files, *unchanged since the 2026-08-13 audit*, so nothing below
is drift. The census is now committed as
[`artifacts/reachability/r3-census.tsv`](../../artifacts/reachability/r3-census.tsv)
and every table in this section is a generated view of it, pinned by
`scripts/check-reachability-census.py`.

<!-- R3-TOTALS:BEGIN generated from artifacts/reachability/r3-census.tsv -->

| corpus | rows | A (reachable) | B (out of fragment) | C (not an obligation) |
|---|---:|---:|---:|---:|
| misconception | 148 | 85 | 16 | 46 |
| technique | 42 | 11 | 19 | 12 |

<!-- R3-TOTALS:END -->

(The misconception row totals 148 rather than 147 because the one deprecated
entry is carried in the file as `DEP`; the live denominator is 147, as before.)

<!-- R3-RANKING:BEGIN generated from artifacts/reachability/r3-census.tsv -->

| fragment it would need | rows | from misconceptions | from techniques |
|---|---:|---:|---:|
| induction-over-nat | 16 | 0 | 16 |
| limits-and-convergence | 7 | 7 | 0 |
| cardinality | 3 | 2 | 1 |
| metatheory | 3 | 3 | 0 |
| extended-reals | 2 | 2 | 0 |
| higher-order-quantification | 1 | 1 | 0 |
| quantified-ring-identities | 1 | 0 | 1 |
| transcendental-reals | 1 | 1 | 0 |
| unbounded-transition-systems | 1 | 0 | 1 |

<!-- R3-RANKING:END -->

**The 17 was wrong in two directions at once, and neither error was findable.**
The 2026-08-13 audit's `census.tsv` was never committed — `RESULT.md` survives
and tells the reader to regenerate the counts with an `awk` line over a file
that does not exist. So the number reached this document and
[`05`](05-the-mathematics-dag.md) with no artifact behind it. Re-derived:

- Its cardinality bucket is "(3): `all-infinities-are-the-same`,
  `you-could-list-them-if-you-tried-harder`, **plus the reals-are-listable
  framing**". That third item is not a corpus row — it is the *second distractor
  form inside* `you-could-list-them-if-you-tried-harder.md`. `grep -ril
  'uncountab\|countabl\|cantor'` over the 148 returns those two files and no
  other. A distractor was counted as a row.
- `infinity-minus-infinity-is-zero` is out of fragment and is in no bucket of
  the 17. Its own file says the stated answer of 0 is wrong and the true limit
  is 5 — an indeterminate form, as squarely `limits-and-convergence` as the
  seven rows that were counted.
- `angle-size-depends-on-arm-length` was declined as "real/trigonometric
  geometry". Measured against the fragment table it is not out of fragment:
  invariance of an angle under positive scaling of either arm is the polynomial
  identity `(u·v)²·|λu|²|μv|² = (λu·μv)²·|u|²|v|²`, which ring normalisation
  decides. Moved to A. This one is a judgment call and is marked `CONTESTED` in
  the census rather than asserted.

Net: **16, not 17**, and the A/B/C split is 85 / 16 / 46 against the audit's
86 / 17 / 44 — both summing to 147, so the disagreement is four specific rows,
not a different denominator. The share of the school corpus we can refute is
**57.8%**, not 58.5%.

Two further corrections from the same measurement. The graph carries **1,567**
concepts, not the 1,566 this document stated in four places above until today:
1,567 files, 1,567 distinct ids, but the default locale collates `C:trend-line`
and `C:trendline` as equal, so `sort -u` reports 1,566 where `LC_ALL=C sort -u`
reports 1,567 — a collation artefact read as a duplicate. And
`truth-table-only-for-hard-problems` is a **second** instance of the defect the
audit reported for `fraction-is-two-numbers-not-one`: its distractor's stated
conclusion ("if it rains I bring an umbrella" and its contrapositive mean the
same thing) is *true*; only the "no need to check" is wrong. A negative-control
suite that treats distractors uniformly would mark a correct answer wrong.

**The adversarial corpus answers a different question, and gives a different
top item.** The 42 `techniques` are not propositions, so they do not stress
which *statements* we can make — they stress which *proof shapes* we can
discharge. Classified the same three ways: 11 reachable, 19 out of fragment, 12
that are search heuristics rather than proof steps (exactly the 12 the corpus
itself marks `epistemic_status: empirical`). And **16 of the 19 want one thing**:
induction over ℕ as a discharged schema — directly (`proof-by-induction`,
`strong-induction`), as an equivalent (`well-ordering`, `infinite-descent`,
`extremal-principle`, `monovariant`), or because the technique's obligation is
schematic in a size parameter (`pigeonhole`, `colouring`, `double-counting`,
`telescoping`, `parity-argument`, `recursion-technique`, `divide-and-conquer`,
`symmetry-argument`, `construction-proof`, `bijection-argument`).

That reorders the roadmap this document was carrying. The school corpus said
**limits first, cardinality second**, and it still does — those are 7 and 3 of
its 16. The techniques corpus says **induction first, by more than a factor of
two**, and induction is the one entry on the ranked list that is *not* a missing
logic: the kernel has an inductive `Nat` with a real ι-computing `Nat.rec`
(`crates/axeyum-lean-kernel/src/nat_prelude.rs`), and R1 above records the
integer prelude at 0 axioms — while the curriculum map records the
`induction` node's fragment as
`LIA / BV (base + step instances)` — **instances, not the schema**. So the
largest single item the mathematics is asking for is not a new theory. It is
closing the loop that already exists, from a goal to an induction schema to a
reconstructed kernel term, without a person writing the proof. That is the
flywheel's own arrow, and it is what the adversarial corpus independently ranks
first.

Two limits on this, stated rather than buried. The techniques corpus is still a
school-and-olympiad corpus — it is adversarial along the *shape* axis, not the
*difficulty* axis, and a research-technique corpus would surface tools
(spectral, homological, model-theoretic) that appear here not at all. And the
A/C boundary in both corpora is a judgment call; the census file says so, and
the B column with its `fragment` values is the part built to be argued with.

**R4 — Close the ordered-field hole so reachability can grow at all.** Until
`Sort::Int`/`Sort::Real` can carry evidence ([`02`](02-the-library.md),
engineering strand `01`), every node above ℕ is unevidenceable in principle, and
R1 will simply strip labels rather than earn them.

## The frontier, stated plainly

axeyum today is a **bounded** reasoner with a strong finite core, an
independently-checkable proof route on four areas, one number system, and a
routing table covering 1.5% of the adjacent concept graph.

That is a defensible position and a much better one than the field average — the
finite core is genuinely strong, and Lean's own kernel accepts its output. But
the ceiling is not set by the solver. It is set by what can be *stated*, and
that is the least-developed rung of the ladder.
