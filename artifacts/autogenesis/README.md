# Autogenesis operation registry

`operations.json` is the reviewed mapping from a fact shape to typed producer,
checker, and admission operations. It contains identifiers and implementation
paths, never caller-authored shell commands.

The first operation is deliberately `counterfactual-fixture-only`. It records
the Nat induction path exercised by the Autogenesis-1 control, but grants no
authority to dispatch or admit an authoritative ledger fact. Run
`python3 scripts/validate-autogenesis-operations.py` after changing it.

`nursery-v1.json` is the leakage-controlled population manifest introduced by
ADR-0478. Its initial two entries are only the frozen Autogenesis-1 longitudinal
regression; they never count toward train, development, held-out, or autonomous
yield. Validate the manifest and print its current readiness gaps with:

```sh
python3 scripts/check-autogenesis-nursery.py
```

Use `--require-ready` only for a Phase 3 evaluation run. It intentionally fails
while the manifest is `foundation-only`; ordinary repository gates require an
accurate report, not a premature green population.
