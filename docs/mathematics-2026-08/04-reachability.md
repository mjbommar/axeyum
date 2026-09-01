# 04 — What this stack cannot yet state

The first three documents ask what we can decide, certify and prove. This one
asks the prior question: **what mathematics can axeyum express at all?**

> **2026-08-31 — this document's answer is missing a producer.** Lane
> `cas-coverage-audit`. "What can axeyum express at all?" is answered here from
> the curriculum DAG and the kernel, and the string `CAS` appears **zero** times
> in 571 lines. `crates/axeyum-cas` is 53 modules and ~77,600 lines of exact
> algebra, and under [ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
> it is **row 3** of every graded statement family: the exact CLASSICAL
> statement, decided where it is decidable, with a re-checkable certificate.
>
> That changes the reachability answer for whole chapters. The classical MVT,
> EVT, IVT, Taylor's theorem with Lagrange remainder, partial-fraction
> decomposition, Gosper and Zeilberger summation, and exact limits of rational
> functions are all *expressible and decided* on the polynomial / rational
> fragment, and none of them are visible from the DAG this document reads.
>
> A reachability claim measured only against the kernel is a claim about ONE of
> three producers (ADR-0601). The chapter-by-chapter version, including where
> the CAS reaches nothing, is
> [`spivak.md`](../curriculum/foundational-books/spivak.md)'s `C` column.

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

> **Both sentences of that last claim were re-measured on 2026-08-17 and both
> are false.** The integer prelude is 0 axioms, and 65 negative-control
> instances over `Sort::Int`/`Sort::Real` run today. The `unreachable!()` is
> still there and still does nothing to evidence. See R4.

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

### The `induction-over-nat` row, measured — and the route is unsound (2026-08-17)

`prove_by_nat_induction` (`crates/axeyum-solver/src/nat_induction.rs`) is the
first solver route built against this row. It is exported at the crate root and
deliberately **not** in `check_auto`'s dispatch. This is the corpus that would
justify wiring it in. It does not: **the route reports `unsat` on three
satisfiable instances, and must not be dispatched until that is fixed.**

Twelve instances, `corpus/regression/uflia_induction/`, each measured three ways
— declared `:status`, the shipped `solve_smtlib` front door, and the induction
route. Harness:
`crates/axeyum-solver/tests/nat_induction_corpus.rs`, run on `s6` with
`--features full` (12 instances, 2 tests; a nonzero instance floor is asserted).

| instance | declared | front door | induction |
|---|---|---|---|
| `guarded_linear_closed_form` | unsat | unknown | **unsat** |
| `guarded_linear_nonneg` | unsat | unknown | **unsat** |
| `guarded_monotone_step` | unsat | unknown | **unsat** |
| `guarded_parity_range` | unsat | timeout | **unsat** |
| `guarded_sum_gauss` | unsat | timeout | timeout |
| `guarded_product_factorial_bound` | unsat | timeout | timeout |
| `guarded_false_base` | sat | unknown | declined |
| `guarded_false_step` | sat | unknown | declined |
| `guarded_wrong_slope` | sat | unknown | declined |
| `unguarded_int_nonneg` | sat | sat | ⚠ **unsat** |
| `unguarded_recurrence_nonneg` | sat | timeout | ⚠ **unsat** |
| `unguarded_int_even_or_odd` | sat | timeout | ⚠ **unsat** |

The front door decides **1 of 12**. The induction route decides 7, of which 6
are instances the front door does not decide — but only **4 of those 6 are
correct**. The other two, plus one head-to-head contradiction, are wrong
verdicts.

**The bug.** The route strips a leading `n >= 0` guard when the goal has one
(`strip_nonneg_guard`) and proceeds *anyway* when it does not. It then
discharges base and step over ℕ while the SMT-LIB quantifier ranges over `Int`.
Any goal true on ℕ and false somewhere below zero is refuted although it is
satisfiable. The minimal reproduction needs no uninterpreted function:

```smt2
(assert (not (forall ((n Int)) (>= n 0))))   ; sat: n = -1
```

Base `0 ≥ 0` and step `k ≥ 0 → k+1 ≥ 0` both discharge, so the route answers
`unsat`. z3 answers `sat`, and **axeyum's own front door answers `sat`** — the
contradiction is visible inside one binary, with no external oracle.

Two things this is not. It is not a shipped wrong verdict: the route is not
reachable from `check_auto` or `solve_smtlib`, which is the one piece of good
news here and the reason "build the corpus before wiring it in" was the right
order. And it is not caught by the route's own suite
(`tests/nat_induction.rs`, 6 tests, all green): every instance there carries the
`(=> (>= n 0) …)` guard, so the suite exercises only the branch that is sound.
A guard *present but unrecognised* (`(> n (- 1))`) is accidentally sound too —
the implication is vacuous below zero — which is why the hole is narrow enough
to have been missed and sharp enough to be a P0 the moment dispatch lands.

The fix has to make non-negativity explicit rather than assumed: decline goals
with no recognised guard, or conjoin `n >= 0` into the conclusion before
discharging. `nat_induction_never_contradicts_declared_status` is committed
**red** against the current route and goes green when either lands.

**What the corpus says about the value case, once the bug is set aside.** The
four correct new decisions are real and are exactly the advertised gap: a closed
form, a lower bound, a monotonicity step, and a parity range, none of which the
front door or z3 decides (z3 returns `unknown`/`timeout` on all six `unsat`
instances). The route also stops cleanly where expected — both nonlinear step
obligations (`sum_gauss`, `factorial_bound`) time out rather than misfire, and
all three false-base / false-step / wrong-slope controls are declined. So the
capability is worth having; it is the domain discipline that is missing, not the
idea.

Two limits on this, stated rather than buried. The techniques corpus is still a
school-and-olympiad corpus — it is adversarial along the *shape* axis, not the
*difficulty* axis, and a research-technique corpus would surface tools
(spectral, homological, model-theoretic) that appear here not at all. And the
A/C boundary in both corpora is a judgment call; the census file says so, and
the B column with its `fragment` values is the part built to be argued with.

**R4 — ~~Close the ordered-field hole so reachability can grow at all.~~
~~ℝ is the only ordered-field hole left, and it now blocks nothing.~~
CLOSED 2026-08-19: ℝ and ℂ are both constructed, at zero trusted declarations.**

The original item read: *"Until `Sort::Int`/`Sort::Real` can carry evidence
([`02`](02-the-library.md), engineering strand `01`), every node above ℕ is
unevidenceable in principle, and R1 will simply strip labels rather than earn
them."* **Re-measured 2026-08-17. Both halves of that premise are false, and the
prediction was already falsified by R1 above** — 19 covered / 19 running / 19
with a negative control, nothing stripped.

### The trusted surface, re-derived

Not read from this document or from `02`, and not from the summary block of the
ledger either: counted from the individual rows of
[`docs/plan/lean-axiom-ledger-v1.json`](../plan/lean-axiom-ledger-v1.json), whose
`entries` are the live trusted declarations and whose `retired_entries` are the
ones that left.

| prelude | trusted surface | live ledger rows | note |
|---|---:|---:|---|
| `nat` | 0 | 0 | |
| `logic` | 0 | 0 | |
| `integer` | 0 | 0 | 34 rows retired 2026-08-15 |
| `rat` | 0 | 0 | not in the ledger when this table was written |
| `creal` | 0 | 0 | the **constructed** ℝ, ADR-0512 |
| `complex` | 0 | 0 | ADR-0521 |
| `string` | ~~1~~ **0** | ~~1~~ **0** | `append` retired 2026-08-17: it is a checked `Definition` by structural recursion, ADR-0513 |
| `real` | 30 | 30 | 8 primitive-interface · 19 external-assumption · 3 derivable-theorem |

**Total: ~~31~~ 30, and all 30 are ℝ** — re-derived 2026-08-19 from the ledger's
rows *and* from the kernel, which this lane could run where the previous one
could not:

```text
cargo run -q --release -p axeyum-lean-kernel \
  --example nat_axiom_inventory -- --include-constructed
complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30
```

The non-real row this table recorded, `axeyum.string.2.append`, is now in
`retired_entries`. Two independent cross-checks from the fact ledger,
which is written by different people at different times than the axiom ledger:
`F:int-euclidean-decomposition`'s footprint evidence records the integer surface
"down from 34", matching the 34 retired rows exactly; and
[`F:ordered-ring-farkas-refutation`](../../artifacts/facts/F-ordered-ring-farkas-refutation.json)
states its generalisation is "quantified over all 30 interface components",
matching the 30 live real rows exactly.

*Not verified when this was written:* the ledger's two `measurement` commands are
cargo examples (`prelude_axiom_inventory`, `nat_axiom_inventory`) and that lane
could not run cargo, so everything above was re-derived from the artifact's rows
and corroborated against the fact ledger. **Both were run on 2026-08-19** and
agree with the corrected table: `prelude_axiom_inventory` emits 30 rows, all
`real`; `nat_axiom_inventory --include-constructed` reports every other prelude
at `axiom=0 opaque=0 quotient=0 total_trusted=0`. The `--include-constructed`
flag is what makes `creal` and `complex` appear at all — without it the tool
answers a question about a different population, which is this repository's
standing trap.

### What "can carry evidence" means operationally — there are two routes, not one

The original premise silently assumed one route. There are two, and they fail and
succeed independently.

**Route A — `axeyum-scenarios::Scenario::self_check`. Still closed, and the
`unreachable!()` is still there.** `check_unsat` establishes an
`Expectation::Unsat` by enumerating the assignment space, and it sizes that space
by calling `sort_bits` over *every* symbol in the arena. `sort_bits` panics on
these sorts — `crates/axeyum-scenarios/src/lib.rs:560-565`:

```rust
Sort::Int => {
    unreachable!("scenarios do not declare integer symbols for enumeration")
}
Sort::Real => {
    unreachable!("scenarios do not declare real symbols for enumeration")
}
```

and identically in `decode_value` at `crates/axeyum-scenarios/src/lib.rs:621-626`.
So an UNSAT *scenario* over ℤ or ℝ would panic before it enumerated anything, and
the source agrees it never happens: all **28** scenarios over those sorts —
`integer_catalog` 7, `real_catalog` 7, `rational_catalog` 8, `real_algebra_catalog`
6 — are `Expectation::Sat`, and the four crate-level tests assert exactly that.
Zero `Expectation::Unsat` appears in `integers.rs`, `reals.rs`, `rationals.rs` or
`real_algebra.rs`.

**Route B — the example-pack / SMT route. Open, and carrying the load.** An
`.smt2` instance goes through `check_auto` to `Evidence::UnsatFarkas`, and the
certificate is re-derived from scratch in exact rationals by a verifier sharing no
code with the elimination that found it. This is what the `math_resource_lra_routes.rs`
suite runs, and it is what R1's "negative control" condition measures. Counted
from `artifacts/ontology/foundational-concepts.json` and the packs on disk:

| node | instances | with a negative control | declaring an `Int`/`Real`-sorted symbol | logic |
|---|---:|---:|---:|---|
| `integers` | 1 | 1 | 1 | `QF_LIA` |
| `rationals` | 24 | 24 | 24 | `QF_LRA` |
| `reals` | 40 | 40 | 40 | `QF_LRA` |

**65 negative-control instances over exactly the two sorts the premise called
inexpressible**, every one of them declaring a symbol of that sort. The
`unreachable!()` is a scope limit on one harness — the finite-enumeration
self-check — not a limit on evidence. Conflating the two is what produced the
original item, and it is the same error as reading a zero from a tool that was
never pointed at the subject.

### Which of ℝ's 30 are load-bearing — 17, and they are all the additive half

Exactly one fact in the ledger carries a `Real.*` axiom footprint:
[`F:schedule-critical-chain-infeasible`](../../artifacts/facts/F-schedule-critical-chain-infeasible.json),
which cites **17** of the 30 (plus 9 per-problem `axeyum.reconstruct.lra.*`
opaques, which are hypothesis and variable constants of that instance, not
prelude). The 17 are the carrier, `add`/`neg`/`zero`/`one`, the additive group
laws, and the order interface. The **13 nothing cites** are the entire
multiplicative interface — `mul`, `mul_assoc`, `mul_comm`, `mul_one`, `mul_zero`,
`mul_nonneg`, `mul_le_mul_of_nonneg_left`, `sq_nonneg`, `left_distrib` (9) — plus
four order laws the linear route happens not to need (`le_trans`, `lt_trans`,
`lt_of_le_of_lt`, `add_lt_add_of_le_of_lt`). That split is not a coincidence: the only route that
reaches the `Real` prelude is *linear* arithmetic, and linear arithmetic never
multiplies two variables.

And the 17 are load-bearing only for a route that has already been superseded.
`F:ordered-ring-farkas-refutation` lambda-abstracts all 30 `Real` constants out of
a term `reconstruct_lra_proof` already built, and the abstracted term **depends on
no axiom whatsoever** — the refutation holds in every ordered commutative ring,
and its footprint checker requires five generalised rows to report size 0 while
five real-specific controls report 18, 22, 24, 7 and 10. So the ordered-field hole
is already closed for the linear route, by generalisation rather than by
construction.

### What R4 now is, and the next step

**R4 is now only about ℝ, and ℝ is not on anyone's critical path.** It is the last
prelude with a trusted surface above 1, that surface is 30, 13 of those rows are
referenced by nothing at all, and the 17 that are referenced are referenced by one
fact that a landed generalisation can already discharge. Nothing is waiting on it:
the nodes above ℕ earn their `covered` labels through route B, which does not
consult the prelude.

Three bounded steps, in order, each independently checkable:

1. **Discharge the three rows the ledger has already assigned.** `Real.lt_trans`,
   `Real.mul_nonneg` and `Real.mul_zero` are classified `derivable-theorem` with
   `discharge_status: planned`, and the retired integer rows carry the derivations
   verbatim (`mul_zero` from `left_distrib` and `add_zero`; `mul_nonneg` by
   instantiating `mul_le_mul_of_nonneg_left` at zero; `lt_trans` from `le_of_lt`
   and `lt_of_lt_of_le`). 30 → 27, and it is bookkeeping the ledger has already
   costed.
2. **Re-route the one fact with a `Real.*` footprint through the ordered-ring
   generalisation.** `F:ordered-ring-farkas-refutation`'s `--require-empty`
   evidence already recovers a specialised statement by instantiation and re-checks
   the application, so the machinery exists; what is missing is applying it to the
   schedule fact. Afterwards **no fact in the ledger has a `Real.*` axiom
   footprint**, and ℝ's entire trusted surface is unreferenced.
3. ~~**Then take the decision `02` step 5 asks for, which becomes cheap.**~~
   **Taken, 2026-08-17/19, and it went the second way.** ℝ *is* built over the ℚ
   that now exists — `CReal`, a Bishop setoid of regular ℚ-sequences under a
   defined equality (**ADR-0512**), 94 declarations at trusted surface 0 — and ℂ
   with it (**ADR-0521**, 39 declarations). This section's advice held up
   exactly as written: nothing was waiting on ℝ, so it was built as a choice and
   not to close a hole, and the 30 rows did not move because they are a
   *different object* from the constructed carrier.

   What the 30 are for is now settled rather than open. They stay as the
   axiomatized interface the constructed carriers are checked *against*, and as
   the negative control for every axiom-freedom claim here — **ADR-0509**,
   "the trusted surface is measured as reached, not only declared". The measured
   version of that: the shipped front door reconstructs over `CReal` with **0
   carrier axioms** where the same three refutations over the `Real` package
   carry 12, 17 and 8, and `arith_prelude_builds()` counts **0** on every
   arithmetic arm of `prove_unsat_to_lean_module`. Delete the 30 and no such
   control exists. Step 1 above (30 → 27) is therefore also no longer obviously
   worth doing: shrinking a control makes it weaker.

**The residue this measurement did surface is about the map, not the prelude.**
The `reals` node advertises `axeyum_fragments = ["LRA / NRA (real-closed
fields)"]`, and **40 of its 40 instances are `(set-logic QF_LRA)`** — zero NRA.
The node named `reals` demonstrates linear rational arithmetic over an abstract
ordered field. That is the same class of overclaim as the quantifier measurement
below, it is invisible to the R1 gate for the same reason, and it is a cheaper
thing to fix than ℝ.

## What "bounded" looks like in the corpus, measured

Measured 2026-08-17, over the 223 instances backing the 19 `covered` nodes
(215 SMT-LIB + 8 DIMACS):

**Zero contain a quantifier.** Not one `(forall …)` or `(exists …)` outside a
comment.

That is the concrete meaning of the frontier statement below, and it is worth
having as a number rather than as an adjective. The corpus does not merely
*happen* to be finite; every proposition the covered curriculum demonstrates is
propositional or quantifier-free.

Two things this is **not**, both checked before writing it down:

- It is not the map overclaiming. `curriculum_induction`'s fragment reads
  `LIA / BV (base + step instances)` — it says *instances*, and it delivers
  instances. Its two packs are a `QF_LIA` contradiction asserting that a finite
  replay over `k = 0..8` found no step counterexample. That is bounded checking
  honestly labelled, not induction mislabelled.
- It is not something the R1 gate catches, and cannot be. R1 asks whether a
  node's family *runs* and whether it *can fail*; both hold here. A pack can
  satisfy both conditions while demonstrating something weaker than the node's
  topic, and no purely structural check distinguishes "exercises the fragment"
  from "exercises the topic". Recorded as a known limit of that gate rather
  than papered over.

A first heuristic for this measurement flagged two nodes and both were false
positives — the `forall` it found in `finite-predicate-v0` is in DIMACS
*comments* describing the encoding, and `relations_and_functions`' "finite
domains" refers to EUF domains, not quantification. The number above excludes
comments.

## The frontier, stated plainly

axeyum today is a **bounded** reasoner with a strong finite core, an
independently-checkable proof route on four areas, ~~two number systems
constructed axiom-free (ℕ and ℤ) with ℚ normalised over them, and one still
axiomatised (ℝ, 30 rows, 13 of them referenced by nothing — R4)~~ — **re-measured
2026-08-19: five number systems constructed axiom-free (ℕ, ℤ, ℚ, ℝ, ℂ), the
whole ladder at trusted surface 0, with the axiomatized `Real` package's 30 rows
retained as the negative control rather than as an unfinished rung (ADR-0509,
ADR-0512, ADR-0521)** — and a routing table covering 1.5% of the adjacent
concept graph.

That is a defensible position and a much better one than the field average — the
finite core is genuinely strong, and Lean's own kernel accepts its output. But
the ceiling is not set by the solver. It is set by what can be *stated*, and
that is the least-developed rung of the ladder.

> **What still bounds "what can be stated", 2026-08-19.** The carriers exist;
> the *analysis* over them does not. No completeness, no suprema, no `sqrt`, no
> cotransitivity of `lt` (~400 lines), no `apart_mul` (~300), no ℂ inverse and
> no `Complex.abs` — the last two because `abs` needs `sqrt` needs completeness.
> Costings and what each unblocks are in
> [`02`](02-the-library.md#what-to-do-first) and the lane notes it cites. The
> rung is no longer least-developed because it is *axiomatized*; it is
> least-developed because it stops at the ordered-field-and-lattice level.
