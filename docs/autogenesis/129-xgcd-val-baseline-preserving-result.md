# Baseline-preserving xgcd projection result

Date: 2026-08-21

## Result

The byte-identical target-owned theorem using only `rfl` compiled successfully,
exported once, and was independently imported by Axeyum twice. Both audit
reports are byte-identical. They report:

```text
root: Axeyum.Autogenesis.xgcdValDirect
footprint: [propext]
direct theorem dependencies: []
```

This is stronger than the earlier official-theorem decline. The proof body is
only reflexivity, so the remaining footprint comes through the public
`xgcd`/`gcdA`/`gcdB` definitional surface itself. Rewriting the official theorem
or descending more theorem dependencies cannot remove it.

The exact three-file checkout baseline matched before execution and after
cleanup. None of those files was opened by the model, changed, or removed; our
three temporary paths are absent.

## Architectural consequence

Stop spending the flywheel on official xgcd wrappers. The bottom-up replacement
must define target-owned coefficients over Axeyum's native gcd carrier, then
prove their linear-combination invariant using the already measured
empty-footprint `Nat.gcd.induction` interface. The official extended-gcd theorem
remains a statement/reference oracle, not an admissible proof dependency.

## Durable evidence

The immutable pack is
`/nas3/data/axeyum/autogenesis/reference-packs/1e74d4601-xgcd-val-baseline-preserving-v1/`.
Its mode-`0444` manifest has SHA-256
`6d5838bded7408ada8a6e1babced0a2eb3d7ee4962c8ed0fe6106a5847d7fe00`;
the directory is mode `0555`. The raw stream remains importer-only.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-baseline-preserving-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_baseline_preserving_reconstruction_result
```
