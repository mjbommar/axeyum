# Subtractive gcd route-frontier audit plan

Date: 2026-08-21

## Decision

Audit the six genuinely new names on the pruned subtraction/zero-base route.
The preceding result derived seven novel dependencies, but one is official
`Nat.sub_add_cancel`: it was already measured as `propext`-bearing and its
primitive-recursive replacement already reconstructed twice with an empty
footprint. Both historical identities are inputs here.

The remaining roots are the private gcd definition equation, the
addition/multiplication gcd equation, and four divisibility lemmas supporting
gcd commutation. They are already present in the immutable export, so this
requires zero exporter invocations and one batch-import read.

## Decision boundary

An empty private definition equation would establish a clean computational
base even if public wrappers remain contaminated. Any assumption-bearing
divisibility roots must be measured or replaced in a later plan; this pass
does not authorize that work.

No proof material is rendered and no replacement, theorem, target, executor,
evaluation, fact, or ledger action is allowed.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-route-frontier-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_route_frontier_audit_plan
```
