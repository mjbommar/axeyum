# Subtractive gcd root audit plan

Date: 2026-08-21

## Decision

Test a division-free foundation for the same balanced-Bézout obligation. The
candidate uses primitive induction on `a + c`, subtracting the smaller positive
argument from the larger and transporting balanced natural coefficients back
through that subtraction.

Before any proof attempt, audit exactly seven official gcd equations: left and
right subtraction, zero bases, one bases, and self gcd. Every root must be
axiom-free before a subtractive Bézout source is authorized.

## Reusable tooling

This is the third batch footprint census in the same dependency descent. The
successor introduces one general read-only tool:

```text
theorem_footprint_batch_audit <sealed-stream> <root>...
```

It reads the stream once, requires every ordered root to be a theorem, and
emits only declaration identities, direct dependencies, footprints, and
aggregate classes. Acceptance remains in the separately frozen plan/result
checker, so generalizing the measurement tool does not generalize authority.

## Boundary

One export and one batch importer pass are allowed, with no retry. Proof terms,
theorem values, source bodies, and raw stream text remain hidden. No Bézout
source, cancellation theorem, Fibonacci target, evaluation, fact, or ledger
operation is authorized by this audit.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-root-audit-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_root_audit_plan
```
