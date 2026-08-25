# 14 — Why the agent attempts ~3 of 146 open facts (reachability × provability)

Status: measured 2026-08-25 (lane `agent-python-layer`). This note answers a
direct question: the fact ledger has ~146 `open` facts, but the agent could
only *attempt* about three of them. That gap is not one bug; it is the product
of two independent bottlenecks, and this note quantifies both and lands the
tool that fixes the first.

## The decomposition

A fact is **attemptable** only if a proof-isolated `lean4export` NDJSON of its
*statement* exists — that frozen export is the only thing a tier-C producer can
be handed (see [03-agentic-layer](03-agentic-layer.md)). It is **provable**
only if one of the two shipped bounded producers (`modeq_family`,
`bounded_induction`) can close the imported goal. Measured over the ledger:

| stage | count | note |
|---|---:|---|
| `open` facts | 146 | the ledger |
| `open` + dependency-ready + train/development | 109 | the eligible pool |
| …with a frozen export today → **attemptable** | **2** | this is the "3" |
| …lean4 + **arrow-free** + no export yet | 41 | the generator can auto-export these |
| …reflexivity-shaped → **provable** by today's producers | 2 | within current producer reach |

So `attemptable ≈ provable ≈ 2–3` is exactly the intersection of *has an
export* and *is refl-shaped*. Neither number is an accident or a config gap.

## Bottleneck 1 — reachability (mostly fixable, tool-capped)

Only a handful of facts ever had a hand-written `.lean` adapter. Every open
fact already carries its statement as `lean4-surface` text, so the adapter is
mechanical: wrap each in a proof-free `def <name> : Prop := <statement>` and let
`lean4export` freeze the elaborated type. `scripts/gen-statement-adapters.py`
does exactly this for a batch, emitting one Lean module plus a
`fact_id → target_def` map. Verified end to end on the pinned Mathlib host (s5,
Lean 4.30.0, Mathlib `c5ea0035…`, lean4export 3.1.0): 24 modeq-family adapters
compiled in one `lake env lean` call, and the arrow-free ones exported to valid
~320 KB NDJSON that `import_statement_ndjson` accepts into a proof-isolated
kernel.

**The tool cap:** lean4export 3.1.0 exits **1, silently (no stderr, no
output)** on any statement whose body reaches a top-level `→` or `↔`, while
arrow-free `∀ vars, atom` statements export normally. Of the 24 modeq facts, 10
are arrow-free (exported) and 14 are arrow-bearing (refused). The generator's
`--exportable-only` flag classifies and drops the arrow-bearing ones so its
output matches what will actually freeze; the census counts 41 arrow-free
open+ready facts, a ~20× expansion of the attemptable set once exported.

## Bottleneck 2 — provability (genuine research, not a gap)

Expanding exports makes facts *attemptable*, not *proved*. The two congruence
facts that did export (`n + a ≡ a [ZMOD n]`, `a + n ≡ a [ZMOD n]`) imported
cleanly and **both producers declined both**:

- `modeq_family`: *"terminal goal is not an Eq/Iff shape this schema's
  refl/symm/trans/Iff.intro combinators can close."* The goal's head is
  `Int.ModEq` (a wrapper def), not the literal `Eq`/`Iff` the combinators match.
- `bounded_induction`: *"terminal goal is not an exact Eq application."*

Unfolding `Int.ModEq n (n+a) a` yields `(n+a) % n = a % n`, which is true but
needs real arithmetic lemmas (`Int.add_mul_emod_self`-class), not reflexivity.
So the modeq **congruence** family is genuinely beyond the current bounded
producers; only the **reflexivity** family (`a ≡ a`) closes today. Raising the
proved count past it requires a richer producer (unfold `ModEq → Eq`, then apply
a bounded arithmetic-lemma search) or importing the Mathlib proof — real
flywheel work, tracked separately from reachability.

## What landed here

- `scripts/gen-statement-adapters.py` — batch adapter generator with
  `--exportable-only` and per-fact classification. Controls:
  `scripts/tests/test_gen_statement_adapters.py`.
- This note, with the measured census and the two decline reasons.

## Next

1. Run the generator over the 41 arrow-free open facts, export on s5, and
   register the NDJSON so `resolve_export` finds them — lifts *attemptable* from
   ~3 to ~43.
2. A `ModEq`-unfolding producer extension to convert congruence goals to `Eq`
   and close them with a bounded lemma search — lifts *provable* past the refl
   family. Soundness-critical; needs its own soundness-negative tests.
3. An arrow-capable export path (newer lean4export, or a different freezer) to
   reach the 14 arrow-bearing modeq facts and the rest of the hypothesis-bearing
   ledger.
