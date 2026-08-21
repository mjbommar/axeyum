# Exact `Int.fib_neg` root audit plan

Date: 2026-08-21

## Decision

Measure the exact official Mathlib 4.30 theorem `Int.fib_neg`, the remaining
open premise of `Int.gcd_fib`, before choosing a reconstruction route. Its
ledger row has no reviewed theorem dependencies, but that absence is catalog
metadata rather than evidence that the proof is independent or axiom-free.

The one permitted root-selected export runs on `s5` against the pinned
Mathlib, Lean, exporter, and compiled module identities. The checkout's three
pre-existing untracked experimental sources are hash-bound and must survive
unchanged. The generic batch auditor may read the resulting stream once and
may emit only names, hashes, direct theorem dependencies, and kernel-derived
axiom footprints. Proof bodies, theorem values, and proof-bearing NDJSON remain
outside model context.

This increment grants no theorem, reconstruction, evaluation, fact-status, or
ledger authority. An empty footprint selects preregistration of exact capsule
composition; an assumption-bearing footprint selects a bounded audit of only
the newly measured direct dependencies.

## Verification

```sh
python3 scripts/check-autogenesis-int-fib-neg-root-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_int_fib_neg_root_audit_plan
```
