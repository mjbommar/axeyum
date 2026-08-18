# Autogenesis operation registry

`operations.json` is the reviewed mapping from a fact shape to typed producer,
checker, and admission operations. It contains identifiers and implementation
paths, never caller-authored shell commands.

The first operation is deliberately `counterfactual-fixture-only`. It records
the Nat induction path exercised by the Autogenesis-1 control, but grants no
authority to dispatch or admit an authoritative ledger fact. Run
`python3 scripts/validate-autogenesis-operations.py` after changing it.
