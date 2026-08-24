# 04 — The tactic catalog: the strategy vocabulary a plan resolves against

Status: landed, 2026-08-24. Slice **A3** of
[`03-agentic-layer.md`](03-agentic-layer.md).

- Catalog: [`artifacts/autogenesis/tactic-catalog-v1.json`](../../artifacts/autogenesis/tactic-catalog-v1.json)
- Schema: [`artifacts/ontology/tactic-catalog.schema.json`](../../artifacts/ontology/tactic-catalog.schema.json)
- Gate: `python3 scripts/validate-tactic-catalog.py` (`just tactic-catalog`)
- Dashboard: [`docs/plan/generated/tactic-catalog.md`](../plan/generated/tactic-catalog.md)

The agent's `Plan` node has to name a strategy, not write prose. This is the
vocabulary it names from: nine tactics extracted from two producers that already
run against a kernel — eight moves of the bounded structural induction producer
and one definitional equivalence-relation combinator from the ModEq family
producer.

## What a tactic entry is

A tactic is a **precondition-guarded move over a kernel goal**, not a target and
not a proof. Every entry answers the same eight questions, and each answer is
checked against something outside the entry:

| Field | What it says | What checks it |
|---|---|---|
| `kind` | closure / induction / rewrite / lemma-splice / elimination / case-split / generalization / combinator | schema enum |
| `precondition.structural` | the typed predicates the goal must satisfy | the predicate vocabulary below |
| `move.kernel_primitives` | the declarations the move builds with | reviewer; the producer's own module doc |
| `residual` | what is left, and the **well-founded measure** it decreases | `shape` and `measure` are `"none"` together or neither |
| `budget` | named Rust constants **with their values** | grepped from the implementing file's own `const` |
| `decline_reasons` | how this tactic can fail | must be variants of *that file's* `DeclineReason` |
| `implemented_by` | crate / path / symbol | the path must exist and declare the symbol |
| `realizes` / `uses_technique` | the overlay capability, the external technique | resolved in the overlay; pinned to the overlay's own `math-education` revision |
| `reach` | the goals it has **actually** accepted and declined | every row cites a module doc, a committed `*-v1.json` result, or a named test |

`assurance` is drawn from the knowledge overlay's enum, deliberately: a reach
row backed by a committed kernel-checked candidate is `independently-checked`;
one backed only by a measurement recorded in the producer's module doc is
`mechanically-observed`. The two are not the same claim and the catalog does not
let them look the same.

## The precondition predicate vocabulary

`precondition.structural` is `{"all_of": [<predicate>, …]}`, and a predicate is
`{"kind": …, "args": {…}}` drawn from a closed table. **There is no free-form
predicate and no name matching** — no regex over declaration names, no fact id,
no `if target == …`. That is the whole point: a tactic that dispatches on a name
is a dispatch-table row and cannot generalize
([doc 228](../autogenesis/228-capsule-lane-retrospective.md)).

| Predicate kind | Args | Means |
|---|---|---|
| `goal-head` | `head` ∈ Eq / Iff / any-prop | the terminal goal's head class; `any-prop` means the goal is never inspected |
| `sides-definitionally-equal` | `value` ∈ true / false | the kernel closes the gap by unfolding alone |
| `binder-shape` | `shape` ∈ zero-succ / ordinary-pi / hypothesis-pi | the shape of a leading `Pi` binder, discovered structurally |
| `hypothesis-family` | `family` ∈ le-shaped / eq-shaped, `index`, `parameter` ∈ zero / succ / any | a retained hypothesis unfolds to an indexed family at that index |
| `hypothesis-state` | `state` ∈ available / stuck / absent | whether an induction hypothesis parses to the goal's shape, was retained unapplied, or is not there |
| `occurrence-embeds` | `needle`, `haystack`, `via` ∈ kabstract-occurrences / app-spine | one term's occurrences can be abstracted out of another |
| `residual-gap-shape` | `shape` ∈ single-argument-diff / multi-argument-diff-same-head / collapsed-occurrence-site | the shape of a leftover `Eq(candidate, expected)` |
| `spine-argument-matches` | `position`, `target` | a top-level argument of the WHNF-reduced spine can equal the goal's right-hand side |
| `head-unfolds` | `via` ∈ whnf-delta, `to` ∈ Eq / Iff | the goal's own head transparently unfolds to a primitive relation |

Adding a predicate kind means adding it to **both** the schema's `predicate`
`oneOf` and `PREDICATES` in the validator; the test suite validates the
committed catalog against the published schema so the two cannot drift.

## The census rule

`scripts/validate-tactic-catalog.py` prints, and its exit status depends on:

```
TACTIC_CATALOG|tactics=N|distinct_precondition_shapes=S|accepted_goals=A|declined_goals=D|realizes_capabilities=C
```

It **fails** when:

- `distinct_precondition_shapes < 2` — a catalog whose entries all match one
  goal shape is a dispatch table wearing a vocabulary's clothes. The count is
  over normalized `all_of` signatures, never over targets.
- any tactic has **zero reach rows** — a tactic with no measured accepted or
  declined goal is a name. Rows come from measurements; there is no way to
  satisfy this by writing a sentence.

Both are census properties of the whole file: no amount of per-field validation
can see either, which is exactly why the checker computes them.

Thirteen rules, thirteen controls in
`scripts/tests/test_validate_tactic_catalog.py`, each mutation-verified in
`scripts/tests/mutation_controls.py` (`python3 scripts/tests/mutation_controls.py
tactic-catalog`) to kill exactly one test.

## How `Plan.tactic_ids` resolves here

`StrategyProposal.tactic_ids` (plan 03, "Tool tiers") is a list of `T:` ids that
must resolve in this catalog. Resolution is not a lookup that ends there:

1. **Resolve.** Each id must be a `status: "active"` tactic in the catalog.
2. **Check the precondition against the goal**, not against the target's name.
   The predicates above are what the A7 mobility census evaluates over every
   open fact *without running a producer*; a plan naming a tactic whose
   precondition the goal cannot satisfy is a plan the deterministic `Gate` node
   can reject before any C tool is reached.
3. **Read `realizes` to get the producer.** `StrategyProposal.producer_id` must
   resolve in `operations.json` or here; the `realizes` capability is the join.
4. **Expect a decline class.** `expected_decline_class` should name a variant in
   the chosen tactic's `decline_reasons`; a decline that is not in that set is a
   finding about the catalog, not about the model.

A plan naming several tactics is naming a *route* — refl closure, then bounded
induction, then an IH congruence rewrite — which is the shape the bounded
induction producer actually takes. Nothing in the catalog is executable; it is a
vocabulary and a set of measured claims about what that vocabulary reaches.

## How reach gets updated

**Only from kernel-labelled runs.** A reach row is a measurement, and the
catalog is the place those measurements are quoted, never made. Concretely:

- An **accepted** row needs either a committed candidate/result artifact under
  `artifacts/autogenesis/` whose state records an independent kernel check
  (`axioms: 0`, a `proof_sha256`), or a statement in the producer's own module
  doc that names what it closed and when it was measured. Cite it in `evidence`.
- A **declined** row needs the same standard: a committed decline artifact with
  its `outcome_class`, or the module doc's own account of what the mechanism
  cannot reach and why. Cite it in `source`, and put the mechanism in `reason` —
  "declines" alone is not a finding.
- A row may **not** be added because a tactic "should" handle a shape. If the
  measurement does not exist, the row does not exist, and the honest state is a
  smaller catalog.
- Moving a row from `mechanically-observed` to `independently-checked` requires
  the artifact, not a re-reading of the doc.

When the producers move out of `crates/axeyum-lean-import/examples/` into
`src/producers/` (another lane's work, in flight), `implemented_by.path` must be
updated **in the same change**: the validator resolves the path and greps the
symbol, so a stale pointer is a red gate rather than a quiet lie. Budget values
are grepped the same way — raising `MAX_BINDERS` in Rust without updating the
catalog fails the gate, which is the behaviour the five bounded-induction family
manifests already have for the same constant.
