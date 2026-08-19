# Factorial-zero family registration

Date: 2026-08-19

## Result

The first one-row surface operation has become a measured two-member family
without becoming a generic proof authority. A single proof-free Lean source now
defines the frozen train propositions

```lean
∀ (n : ℕ), n.ascFactorial 0 = 1
∀ (n : ℕ), n.descFactorial 0 = 1
```

as transparent `Prop` values. Pinned Mathlib v4.30.0 exports each definition in
isolation. Fresh Axeyum importer/kernel instances reproduce the goal and proof
identities from the sealed 138-row census.

| Member | Declarations | Binders / nodes | Axioms / theorems | Ledger state |
|---|---:|---:|---:|---|
| `Nat.ascFactorial_zero` | 55 | 1 / 4 | 0 / 0 | already proved |
| `Nat.descFactorial_zero` | 59 | 1 / 4 | 0 / 0 | open |

The family checker opens no held-out fact, requests no Mathlib proof body, and
performs no ledger write. The two external streams remain read-only under
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-factorial-zero-family-v1/`;
Git stores only their identities and the small proof-free source.

## Authority boundary

Reuse applies to the adapter source and bounded reflexivity producer. Admission
authority remains exact. The new
`authoritative-mathlib-nat-descfactorial-zero-reflexivity-v1` registry row binds
only `F:ml430-nat-descfactorial-zero-966b01df`, its immutable descendant stream,
target, goal, proof, budgets, and empty dependency result. The first fact keeps
its historical operation unchanged.

The frontier-derived gate coupling names the family checker itself. That mention
is reviewed explicitly: the checker accepts only the open prestate or an exact
operation-bound proved state, so closing the fact strengthens rather than
invalidates the gate. Any new or stale script mention blocks dispatch.

This is deliberately smaller than a generic equality operation. Seven rows in
the same census reached the producer but failed independent kernel checking;
114 more still require a proof-free type slice before any producer may run.

## Next boundary

Registration is not proof credit. From this clean registration commit, let the
machine frontier select the still-open fact, execute the exact operation,
prepare its typed transaction, stop after durable intent, recover, replay the
settled fact in a clean worktree, and derive the readiness delta. Only that
sequence may change the ledger.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_factorial_zero_family
python3 scripts/check-autogenesis-factorial-zero-family.py
python3 scripts/validate-autogenesis-operations.py
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
