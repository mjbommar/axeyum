# Current-stable Mathlib statement comparison plan

Date: 2026-08-20

## Correction and decision

The earlier source note proposed a v4.33 comparison. Current official release
metadata instead marks Mathlib `v4.32.1` as the latest stable release and
`v4.33.0-rc1` as a prerelease. The comparison is therefore pinned to stable
Mathlib `v4.32.1` at commit
`520045ab14e26149ee970e2e617ca04b09bde5d6` and Lean `v4.32.1` at commit
`f054605aea4b840552cca2e725580bffd1e1b704`.

The existing v4.30.0 inventory remains Axeyum's importer-compatible baseline.
This increment measures version survival; it does not silently migrate or mix
the two environments.

## Fixed sequence

One shallow external checkout and one statement-only extraction are permitted.
The exact unchanged extractor may inspect theorem declarations and serialize
only names, modules, universe parameters, pretty types, and structural type
representations. It may not evaluate or serialize theorem values.

The new bulk inventory remains outside Git and becomes read-only after an
independent schema/order/scope/proof-field audit. The tracked result will
classify each of the existing 240 selected names as absent, structurally
identical, pretty-type-only drift, structural drift, or module-only drift.

Only the small comparison manifest, checker, tests, documentation, and external
inventory identity belong in Git. No full lean4export rerun is required.

## Authority boundary

The plan permits no extractor compatibility patch or retry. If the exact v4.30
extractor no longer compiles against 4.32.1, the run declines and records that
version boundary rather than adapting the extractor after seeing the result.

No proof body, theorem value, proof import, proof search, kernel theorem
submission, executor invocation, fact transition, evaluation credit, or ledger
write is authorized.

## Verification

```sh
python3 scripts/check-autogenesis-mathlib-current-stable-statement-comparison-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_mathlib_current_stable_statement_comparison_plan
```

The exact tags, commits, paths, sequence, and ceiling are in
[`mathlib-current-stable-statement-comparison-plan-v1.json`](../../artifacts/autogenesis/mathlib-current-stable-statement-comparison-plan-v1.json).
