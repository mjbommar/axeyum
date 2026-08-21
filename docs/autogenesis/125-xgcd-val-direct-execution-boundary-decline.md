# Direct xgcd projection execution-boundary decline

Date: 2026-08-21

## Result

The one permitted compilation exited before theorem elaboration. Lean requires
an input module compiled through this package environment to be contained under
the Mathlib package root; the sealed NAS source path was outside it.

This result says **nothing** about whether `rfl` proves the projection equation.
No olean was produced, lean4export did not run, Axeyum imported no stream, and no
projection or ledger credit was granted. The no-retry rule was honored rather
than disguising an execution mistake as another attempt.

## Correct next boundary

A new preregistration may copy the byte-identical tracked source to one exact
temporary filename under the clean pinned Mathlib root, compile it once, and
remove only that named source plus its named olean/ilean after their identities
are sealed. It must verify the checkout is clean before and after, so an
execution workaround cannot contaminate the shared reference environment.

## Durable evidence

The immutable decline pack is
`/nas3/data/axeyum/autogenesis/reference-packs/17cf9888b-xgcd-val-direct-v1/`.
Its mode-`0444` manifest has SHA-256
`9192ab6af236f36f68d16f59e1cc4ada80b2f22dae4dc740a945f93f7d0613c6`;
the directory is mode `0555`. The 199-byte diagnostic is sealed by hash and
classified as pre-elaboration infrastructure evidence.

## Verification

```sh
python3 scripts/check-autogenesis-xgcd-val-direct-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_xgcd_val_direct_reconstruction_result
```
