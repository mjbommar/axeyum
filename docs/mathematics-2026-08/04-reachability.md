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

## The 23-node map against the 1,566-concept graph

The sibling `math-education` repository carries **1,566 concepts**, 148
misconceptions, 88 people, 61 works and 42 techniques, over an RDF/OWL/SKOS
ontology with content authored in YAML and projected into the vocabulary.

The curriculum is the **routing table** that should connect that content to
axeyum's decidable fragments. It has 23 entries against 1,566 concepts — a ratio
of roughly 1:68. The claim ledger already references the graph (435 concept
refs, now all resolved and pinned), so the wiring exists; the routing table is
simply almost empty.

That is not an argument for 1,566 curriculum nodes. It is an argument that
**nobody has asked, systematically, which mathematics this stack can reach** —
and the corpus audit is the only time anyone has: of 148 misconceptions, **86
(58.5%) were formalisable and refutable, 17 were out of fragment, 44 were not
checkable propositions at all.** That is the first honest reachability
measurement the project has, and its author flagged the caveat that a
*school*-mathematics corpus overlaps our fragments by construction, so 58.5%
measures that corpus rather than "real mathematical error".

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
already *name the fragment each would need*. Those 17 rows are a
ranked feature request written by the mathematics itself.

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
