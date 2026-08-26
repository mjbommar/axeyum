# Ranked proposition compatibility and graph reconciliation

Date: 2026-08-26

## Result

The first held-out-safe ranked proposition census compares 684 candidate pairs
across all 57 train/development goals in the corrected open fixed-palette
population. It finds six exact cross-kernel definitional matches, 678 declines,
zero audit errors, and zero held-out accesses.

The six matches are five binomial statements and one factorial positivity
statement. They are not newly proved by Autogenesis: independent native kernel
development already constructed the theorem terms. The finding was that the
Mathlib-derived statement records and native library declarations were not
connected strongly enough for retrieval and accounting to recognize that
existing work. The six records have now been reconciled through checked,
operation-free transactions; the result remains explicitly non-autonomous.

The durable observation is
[`open-ranked-proposition-census-v1.json`](../../artifacts/autogenesis/open-ranked-proposition-census-v1.json).
It binds the candidate ranking, corrected population, and every external
statement-capsule size and SHA-256. The external NDJSON remains outside Git.
The immutable pre-reconciliation ranking is
[`open-lemma-candidate-ranking-pre-reconciliation-v1.json`](../../artifacts/autogenesis/open-lemma-candidate-ranking-pre-reconciliation-v1.json).
The checked transition result is
[`proposition-reconciliation-result-v1.json`](../../artifacts/autogenesis/proposition-reconciliation-result-v1.json),
and the post-reconciliation rerun is
[`open-ranked-proposition-census-v2.json`](../../artifacts/autogenesis/open-ranked-proposition-census-v2.json):
51 goals, 612 candidate pairs, zero exact matches, and zero held-out access.

## What is checked

[`checked_proposition_compatibility`](../../crates/axeyum-lean-import/src/theorem_composition.rs)
accepts two independently owned kernels and two closed proposition expressions.
It:

1. independently infers that each expression inhabits `Prop`;
2. translates the source proposition into a private target clone by exact
   rendered declaration names;
3. re-infers the translated expression in the target kernel; and
4. requires target-kernel definitional equality with the imported goal.

This is deliberately different from comparing declaration types. A proof-free
goal is encoded as `definition : Prop := statement`; comparing only its outer
type would declare every such goal compatible because all have type `Prop`.
The negative control (`Nat.choose_zero_right` against the `Nat.choose_self`
goal) is rejected while the independent `Nat.choose_self` construction is
accepted.

## Graph meaning

The knowledge overlay adds the qualified relation `definitionally-matches`
from a fact to a kernel declaration. The six links are
`independently-checked`, but their semantics explicitly grant no proof,
operation, fact-transition, or admission authority. This is the missing
representation edge in the longer chain:

```text
Mathlib source proposition
  -> proof-free imported goal
  -> definitionally-matches
  -> native kernel theorem
  -> existing native fact, when one exists
```

This edge is not a theorem correspondence. The correspondence schema requires
two settled fact endpoints and describes equality of mathematical content
between facts. Here the source fact remains open and the target is a kernel
declaration. Forcing these observations into that schema would either invent a
fact transition or weaken a useful settled-endpoint invariant.

## What comes next

1. Add native fact records for `Nat.choose_succ_self_eq_zero` and
   `Nat.zero_choose_succ`, which are presently among the unlinked kernel
   theorems. Their statements, dependencies, and empty footprints must be read
   from the kernel rather than copied from the imported goals.
2. Define a reviewed reconciliation transaction that can settle an open
   statement-source fact from an independently checked native theorem plus an
   exact proposition-match receipt. It must record `no_operation` and
   non-autonomous provenance; graph cleanup must never become production
   credit.
3. Apply that transaction to these six controls, then regenerate the open
   population, lemma ranking, kernel/fact linkage, and coverage views together.
4. Rerun the same ranked compatibility census on the remaining population.
   The meaningful producer denominator excludes reconciled duplicates; the
   discovery artifact remains immutable evidence of why each row moved.
5. Expand the audit kernel beyond the current Int/Nat prelude only when the
   candidate ranking contains a measured demand from another family. Missing
   declarations remain typed declines, not approximate matches.

The immediate lesson is strategic: improving premise retrieval is necessary,
but theorem construction and graph reconciliation must be measured separately.
Six of 57 goals were already solved mathematics hidden by missing connective
tissue; the other 51 remain genuine producer targets under this ranked window.
