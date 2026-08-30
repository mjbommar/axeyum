# 347 — vocab two writers

<!-- plan-section: lane-status -->

**DONE.** `artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` had two
writers and the poorer one deleted `bridge_provenance` and `row_digest` at
exit 0, while the failing `--check` advised exactly that. The file now has one
owner, the red is cleared, and the shape is gated
([ADR-0652](../../research/09-decisions/adr-0652-one-producer-per-key-a-generated-artifact-has-exactly-one-writer.md)).

**Why `--check` was red — it was right about staleness and wrong only about
the remedy.** The two producers agree **element for element** on `bridge` (72)
and `settled` (174), the whole substantive derivation. The refill generator's
document is a strict SUBSET: no `bridge_provenance`, no `row_digest`, none of
the four `bridge_*` coverage counts, shorter `derivation`. So the staleness was
real and was caused entirely by the second writer knowing less — the two never
disagreed about the mathematics. Reproduced at `main` in a `git archive` scratch
tree: sha `096d8c85` -> `27205641`, both keys gone, **exit 0**.

**Who owns it now.** `gen-autogenesis-statable-vocabulary.py`, alone.
`gen-autogenesis-nursery-refill.py` READS the artifact and cross-checks it
against its own independent derivation (constants from the pinned inventory's
`type_repr` rather than the cached constants file), raising instead of
overwriting on disagreement. `VOCABULARY` is out of its `outputs` map. Verified
both ways in a scratch tree: a real draw run leaves the file byte-identical;
a one-entry perturbation gives exit 1 naming the owning generator.

**What the new guard refuses** —
`scripts/check-generated-artifact-ownership.py`, ~10 s, 5 producers executed,
registered in **both** aggregate gates (`check-aggregate-scope.sh` green,
410/466 steps, 66 recorded differences, no new one):

| arm | refuses |
| --- | --- |
| `KEYS` | the artifact missing any key its owner derives, top level or nested |
| `KNOWN` | a script naming a guarded artifact that is not classified, or a classification the tree no longer matches |
| `READS` | a declared read-only script containing any write call (AST) |
| `RUNS` | a non-owner producer, EXECUTED in a sandbox, leaving it anything but byte-identical |
| `CTRL` | a RUNS arm that accepts a planted second writer |
| `OWNER` | an owner that cannot restore a perturbed copy byte for byte |

`RUNS` is empirical because the destroying write reached the path through a
dict value (`outputs = {VOCABULARY: …}` then `path.write_text(text)`), which
any receiver analysis a person would write misses. `KNOWN` derives its script
set from the tree, so a NEW writer goes red rather than unmeasured. The gate
classifies itself as a producer and bounds its own nesting.

Detail moved to [`../notes/347-vocab-two-writers.md`](../notes/347-vocab-two-writers.md).

