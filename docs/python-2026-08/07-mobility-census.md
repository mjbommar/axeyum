# 07 — The mobility census: what the tactic vocabulary can reach, measured without a model

Status: landed, 2026-08-24. Slice A7 of
[`03-agentic-layer.md`](03-agentic-layer.md). Subject: the nine tactics of
[`04-tactic-catalog.md`](04-tactic-catalog.md) against the 191 open facts of
`artifacts/facts/`.

## The question A4 could not answer

A4 closed the loop: a model chose a tactic, a deterministic gate passed the
plan, a producer searched, a kernel admitted, and a second kernel re-derived the
term with an empty axiom footprint. It also produced a number nobody could
interpret. Of three exportable facts the model routed two and emitted
`NoGeneralRoute` for the third — a **measured false negative**, since all three
close in milliseconds. The generality rule filters on the model's *confidence
that a route generalizes*, not on whether it does, and A4's finding 3 said the
gap between those was 1 in 3 and needed measuring properly.

That is what this census is. It takes the model out of the loop entirely and
asks a purely structural question: **for each tactic and each open fact, does
the tactic's precondition hold at that fact's goal?** No producer runs. No
search happens. Nothing is admitted.

## Three answers, not two

The result of one (fact, tactic) pair is `matched`, `unmatched(reason)`, or
`unevaluable(reason)` — never a bool.

The distinction is the whole point, and it is not defensive coding. CLAUDE.md
records the shape: *an empty result from a tool that was never pointed at your
subject is indistinguishable from a strong negative result.* **187 of the 191
open facts have no frozen statement export on this host.** A two-valued census
would have reported all 187 as zero-match, the capability backlog would have
been 187 facts deep, and every entry in it would have been a fiction — no
capability removes an obstruction that was never measured.

So a fact with no kernel goal is `unevaluable`, is counted separately, and never
appears in a cluster.

## Where a goal comes from

One route, digest-pinned, and no fallback:

1. `axeyum.agent.tools.resolve_export` resolves the fact to a committed
   statement-adapter manifest or to
   `artifacts/autogenesis/agent-frozen-export-index-v1.json`, re-hashes the
   bytes, and refuses on a mismatch.
2. `axeyum.producers.import_statement_ndjson` imports it into a real kernel.
3. The census evaluates the resulting `ExprId`.

There is deliberately **no** step that parses `formal.statement` Lean text into
a term. Every fact carries one (185 in `lean4-surface`, 6 in `smtlib2`), and
using it would have made the census evaluate 191 facts instead of 4 — at the
cost of every verdict resting on a goal nobody pinned. That is the
`explain_corpus` failure in a new place: a plausible verdict that cannot be
traced to a checked artifact.

## The predicate vocabulary

`artifacts/ontology/tactic-catalog.schema.json` enumerates nine predicate kinds.
All nine are implemented in `python/axeyum/agent/mobility.py`, and
`test_every_schema_predicate_kind_is_implemented` asserts set equality against
the schema — an unimplemented kind would be silently skipped, which reads as
"satisfied".

| kind | how it is decided at the initial goal |
|---|---|
| `goal-head` | the app-spine head of the conclusion, classified as `Eq`-shaped / `Iff`-shaped / any Prop |
| `sides-definitionally-equal` | `Kernel.def_eq` on the equation's two sides |
| `binder-shape` | a leading Pi binder whose domain is zero/succ-shaped, a data binder, or a Prop binder |
| `hypothesis-family` | a Prop-domain leading binder whose type is `le-shaped` or `eq-shaped`, with its index and parameter classified as `zero` / `succ` / other |
| `hypothesis-state` | whether an equation-shaped hypothesis agrees with the goal's carrier (`available`), disagrees (`stuck`), or is absent |
| `occurrence-embeds` | a hypothesis side found among the reachable subterms (`kabstract-occurrences`) or the top-level spine arguments (`app-spine`) of a goal side |
| `residual-gap-shape` | **unevaluable** — see below |
| `spine-argument-matches` | a top-level argument of the goal's lhs that is `def_eq` to its rhs |
| `head-unfolds` | `Kernel.whnf` of the conclusion, then the head classified as above |

**Structure, never names.** The schema says a tactic that dispatches on a
declaration name is a dispatch table entry, not a producer, and the evaluator
holds to that: `Environment` discovers zero/succ-shaped, `le`-shaped,
`Eq`-shaped and `Iff`-shaped families the way
`crates/axeyum-lean-import/src/producers/bounded_induction.rs`'s
`detect_nat_shape` / `detect_le_shape` do — by constructor arity, field
recursion and conclusion shape read out of the environment. The words `Nat`,
`Nat.le`, `Eq` and `Iff` appear nowhere in the detection code.

### The mid-derivation predicates

`residual-gap-shape` describes the leftover `Eq(candidate, expected)` a
congruence wrap did not close, and the `candidate-argument` /
`expected-argument` sites of `occurrence-embeds` name the same state. **That
state does not exist before the move runs.** At an initial goal they answer
`unevaluable("requires-mid-derivation-state")`, never `unmatched`. Reporting a
zero there would have understated two tactics' reach with a number that looked
measured.

`all_of` aggregation prefers `unmatched` over `unevaluable`: a violated conjunct
is a sound NO whatever the others say, and the census would rather place a fact
in a named cluster than in the unevaluable bucket.

## What was measured

```
MOBILITY|open=191|evaluable=4|unevaluable=187|tactics=9|matched_pairs=2|zero_match_facts=2|clusters=2|held_out_excluded=57
```

| bucket | facts |
|---|---|
| open | 191 |
| evaluable (a frozen export imported) | 4 |
| unevaluable (never looked at) | 187 |
| zero-match among the evaluable | 2 |
| held-out, counted and never named | 57 |

**The headline is the second row, and it is the same finding A4 recorded as
`retrieval-miss`, now measured over the whole ledger rather than one page.**
A4 counted 3 of 98 dependency-ready non-held-out facts; over all 191 open facts
it is 4 of 191 — `Nat.ModEq` refl, symm, trans and comm, all `development`, all
from the same adapter run. Nothing else in the ledger has a proof-free statement
export a producer can import. The bottleneck between here and volume is the Lean
export step, not the tactic vocabulary, and no capability listed in any backlog
moves one of the 187.

The generated dashboard is
[`docs/plan/generated/mobility-census.md`](../plan/generated/mobility-census.md);
the artifact is `artifacts/autogenesis/mobility-census-v1.json`.

## Held-out isolation

`artifacts/autogenesis/nursery-v1.json` preregisters a blind held-out
population, and CLAUDE.md records what one leaked id costs: 19 of 76 held-out
propositions, 25% of the partition, for one theorem. 57 of the open facts are
held-out.

They are **counted and never named**. `totals.held_out_excluded` and the
`held-out` row of the partition table are the only places they appear, as
integers. The writer then re-scans the serialized document for every held-out id
and refuses to write on a hit (`assert_no_held_out`), the committed checker
repeats the scan as a text walk over the whole file, and
`check-autogenesis-holdout-isolation.py` scans it a third time as one of 1022
artifacts. Both scans have positive controls: a document that *does* carry one
must be rejected, or the guard is decoration.

## The reach cross-check

The catalog records MEASURED reach as `reach.accepted_goals`. Re-evaluating
every row that cites a fact id is a two-way test: a `Matched` confirms the
evaluator against an independent claim, and an `Unmatched` is either a bug here
or a reach the catalog does not have.

```
REACH|rows=21|evaluable=16|disagreements=7|initial_goal_disagreements=4
```

Rows are classified by comparing the catalog's own `goal` text to the ledger's
`formal.statement` — structurally, not by reading prose:

- **3 `sub-goal` disagreements**, all `T:ih-congruence-rewrite`, whose rows say
  "succ case of ∀ (n : ℕ), …". They record that the tactic fired on a subgoal
  reached *after* an induction. The census evaluates initial goals, so these are
  a population mismatch and not a defect in either artifact.
- **4 `initial-goal` disagreements**, which are real and are listed for the
  coordinator rather than repaired here (the catalog is another lane's file, and
  an evaluator that edited its own oracle would be worthless):

| tactic | fact | evaluator said |
|---|---|---|
| `T:residual-lemma-splice` | `F:ml430-nat-zero-ascfactorial-af4fcdca` | `no-equation-shaped-hypothesis` |
| `T:residual-lemma-splice` | `F:ml430-nat-one-ascfactorial-8bacb017` | `no-equation-shaped-hypothesis` |
| `T:modeq-equivalence-combinators` | `F:ml430-int-modeq-refl-30e15520` | `no-equation-shaped-hypothesis` |
| `T:modeq-equivalence-combinators` | `F:ml430-int-modeq-comm-1e4bcc07` | `goal-does-not-unfold-to-an-eq-shaped-head` |

Both classes have the same reading. `T:residual-lemma-splice`'s precondition
demands `hypothesis-state: available`, which is an *induction* hypothesis; its
two accepted rows cite the whole fact, where no hypothesis exists until the
induction runs. `T:modeq-equivalence-combinators` demands `head-unfolds → Eq`
and an available hypothesis, but its own title is "eq-**iff** combinators" and
two of its four accepted goals are reflexivity (no hypothesis) and an `Iff`
(does not unfold to `Eq`). The precondition as written admits neither. Whether
the fix is an `any_of`, a second tactic, or a narrower reach claim is a decision
for the catalog's owner.

**The 12 rows that agree are the load-bearing half.** Five
`T:bounded-structural-induction` rows, two `T:refl-closure` rows and two
`T:modeq-equivalence-combinators` rows were confirmed by an evaluator that has
never seen the producer, over goals imported from digest-pinned Lean exports.

## Must-decline sampling

Nine non-held-out `generated-mutation` rows in the nursery are FALSE by a
counterexample that `check-autogenesis-must-decline-population.py` recomputes
rather than trusts. A tactic whose precondition admits one is flagged `SUSPECT`.

```
MUST_DECLINE|rows=9|evaluable=0|unevaluable=9|suspect=0
```

**`suspect = 0` here means nothing was looked at.** None of the nine has a frozen
statement export, so the negative control has no subject on this host — and a
sampling rule that reported "clean" from an empty subject would be precisely the
checker-that-cannot-fail this repository refuses. So
`python -m axeyum.agent mobility --must-decline` exits **2** in that state,
distinct from **1** (a real suspect) and **0** (evaluated, and clean). Producing
exports for those nine is the cheapest way to make the control real, and it is a
smaller job than the 187.

## Re-measured 2026-08-30: the census has no subject left

Everything above is what was measured on 2026-08-24 and it is still an accurate
record of that run. **It is no longer a description of the ledger**, and the
gate now says so in three lines instead of 126.

126 of the 152 written fact rows have since been **proved**. That is the
flywheel working, and the checker used to reject each one — 126 identical
`is proved in the ledger; the census is over OPEN facts` lines out of 127 total,
which reddened `just check` for a long time and buried the one finding that
mattered. [ADR-0618](../research/09-decisions/adr-0618-graduation-is-lifecycle-a-census-dies-when-its-subject-closes.md)
makes graduation a counted, audited lifecycle event instead.

The finding underneath, every number recomputed from the ledger, the nursery and
the export index rather than read out of the census:

| | 2026-08-24 | 2026-08-30 |
|---|---:|---:|
| open facts | 191 | 146 |
| census rows | 187 | 152 (26 still open, 126 graduated) |
| evaluable | 4 | 3 written, **0 still open** |
| zero-match clusters | 2 | 1, naming **no** still-open fact |
| entries in the frozen-export index | 4 | 4, **none** whose fact is still open |

**A frozen export is the only route to an evaluable goal** — that is the
deliberate choice argued in "Where a goal comes from" above, and it is what
makes this state terminal for the artifact. With zero open facts carrying one,
regenerating produces `evaluable = 0`, which rule 7 already refuses. So
`just mobility-census-regen` is not the remedy here; a producer exporting a
statement for a fact that is **still open** is.

Read the headline row the same way as before, and note the direction it moved.
The 2026-08-24 finding was that the bottleneck between here and volume is the
Lean export step, not the tactic vocabulary. Since then 126 censused facts
closed by other routes and the export index gained **nothing**. The bottleneck
did not narrow; the ledger walked around it.

The status line carries both sides so the gap is legible:

```
MOBILITY_CENSUS|open=189|evaluable=3|…|live=26|graduated=126|live_evaluable=0|live_exportable=0|audit=ok|violations=3
```

`open` and `evaluable` are what the census CLAIMED when it ran; `live*` and
`graduated` are recomputed now. `audit=ok` means every row's status was re-read
at the census's pinned commit and all 152 were genuinely `open` there — the
census did not pad its population. `audit=no-git` (a `git archive` snapshot)
means the audit could not run and says so rather than passing quietly.

## Commands and gates

```sh
# regenerate (needs the compiled kernel, the agent extra, and /nas3 exports)
uv run --no-sync python -m axeyum.agent mobility --write
uv run --no-sync python -m axeyum.agent mobility --reach-check
uv run --no-sync python -m axeyum.agent mobility --must-decline

# validate the committed file (standard library only)
python3 scripts/check-mobility-census.py
python3 -m unittest scripts.tests.test_check_mobility_census
just mobility-census                     # both of the above
python3 scripts/tests/mutation_controls.py mobility-census
```

`just check` and `scripts/check.sh` run the checker and its controls and
**never** regenerate. A gate that regenerated its own subject would agree with
itself whatever the tree said — and the census needs a compiled kernel and
`/nas3`, neither of which a standard-library gate may require.

The checker recomputes the catalog, nursery and export-index digests from disk,
walks the document for held-out ids, checks every fact id against
`artifacts/facts/` for existence *and* `open` status, and reconciles every
counter against the rows it summarizes. Its 39 guards are each
mutation-verified to kill exactly one test.

The rule that carries the most weight is `evaluable > 0`, enforced twice on
purpose — in the generator (the run exits 1) and in the checker (the artifact is
void). A census that evaluated nothing is not a census, and on this ledger that
is one bad export path away from being the state of the world.

## What A5 inherits

1. **The capability backlog is not a tactic backlog.** 187 of 191 open facts are
   blocked on a retrieval step, and 2 of the 4 remaining are zero-match. Any
   dashboard answering "which capability removes the largest measured cluster?"
   must answer "an export pipeline" before it answers with a tactic, or it is
   ranking the wrong axis.
2. **`unevaluable` is a first-class obstruction class.** A5's `Classify` node
   maps `Decline` objects to the AG4.1 taxonomy; `retrieval-miss` is already in
   it and this census says it dominates by two orders of magnitude.
3. **Two catalog preconditions are narrower than their own measured reach.**
   The four `initial-goal` disagreements above are a concrete, bounded piece of
   work for whoever owns `tactic-catalog-v1.json`.
4. **The nine must-decline rows are the cheapest high-value export target.**
   Nine exports turn a control that currently cannot fail into one that can.
