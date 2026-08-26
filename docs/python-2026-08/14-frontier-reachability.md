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
| facts already `proved` | 498 | the closed frontier — the refl/symm/trans/comm families (nat *and* int) are here |
| `open` facts | 146 | the remaining frontier |
| `open` + dependency-ready + train/development | 109 | the eligible pool |
| …with a frozen export today → **attemptable** | **2** | this is the "3": `nat-modeq-symm`, `nat-modeq-trans` |
| …lean4 + **arrow-free** + no export yet | 41 | the generator can auto-export these |
| …arrow-free open facts the producers actually **close** | ~0 | the provable shapes are already proved |

The sharp finding: the "3" is not a floor set by *reachability*. The refl /
symm / trans / comm shapes the two bounded producers can close are **already
proved** (498 of them) — the four unregistered `int-modeq-{refl,symm,trans,comm}`
NDJSON on the NAS all correspond to `proved` facts. Every arrow-free *open*
modeq fact I exported and handed to a producer was a **congruence** goal
(`n + a ≡ a`, `a + n ≡ a`) and was **declined**. So `attemptable ≈ 3` is
dominated by the *provability* bottleneck, not reachability: expanding exports
adds attempts (and typed obstruction data), but the open frontier now needs
proof strategies the producers do not have.

Which bottleneck dominates depends on the fact. For the modeq family the
provability wall is in front of the reachability one, so exporting more of it
buys attempts, not proofs. For families whose *provable* shapes are **not** yet
proved, reachability is the binding constraint and the generator directly lifts
the proved count. Both levers are real; this note lands the reachability tool
and measures where each wall stands today.

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

**Correction, 2026-08-26:** this was not a tool cap. The empty-file experiment
conflated s5 output/storage handling with exporter semantics. Streaming stdout
off the host, with the exact same lean4export 3.1.0, Lean 4.30.0 and Mathlib
commit, exported three implication-bearing binomial statements. All three then
passed Axeyum's proof-isolated importer with zero axioms and zero exposed theorem
proofs. The generator's `--exportable-only` flag remains solely to reproduce
the older 41-row census; it must not be used as a current reachability filter.
See the checked
[`binomial arrow capability`](../../artifacts/autogenesis/binomial-arrow-export-capability-v1.json).

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
3. Batch and index the now-exportable arrow-bearing statements using streamed
   output and hash-bound external packs; do not vendor the NDJSON into Git.
