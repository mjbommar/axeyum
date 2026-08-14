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
names a family that runs. Four nodes name none today; three of those are the
number systems. This is cheap and it converts the map from assertion to
measurement.

**R2 — Make `bounded` say what it is bounded *by*.** Sixteen nodes share one
word covering very different situations: bounded by bit width, by enumeration
domain, by an admission cap like `MAX_CROSS_PRODUCTS`, or by a resource budget.
Those have different fixes and different frontiers, and collapsing them hides
exactly where the ceiling is.

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
