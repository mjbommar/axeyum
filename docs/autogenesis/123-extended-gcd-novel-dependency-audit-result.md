# Extended-gcd novel-dependency audit result

Date: 2026-08-21

## Result

The one preregistered batch pass classified all seventeen previously
unmeasured dependencies:

- 6 empty-footprint;
- 1 Quotient-bearing without `propext`;
- 10 `propext`-bearing.

This closes the **imported** xgcd route. `Nat.xgcd.eq_1`, like the previously
measured `Nat.xgcd_val`, carries `propext` and has no direct theorem dependency.
No further imported theorem descent can clean either projection equation.

The mathematical route remains open because `Nat.gcd.induction` is
empty-footprint. Its only direct theorem dependencies are `Nat.mod_lt` and
`Nat.succ_pos`; the former already has a native axiom-free replacement in the
target. This is the right bottom-up interface for a target-owned extended-gcd
construction.

## Sequencing

The next increment should preregister the smallest proof-free projection probe:
test whether the statement

```text
∀ (x y : ℕ), x.xgcd y = (x.gcdA y, x.gcdB y)
```

can be reconstructed transparently without the official theorem. If that
definition-level seam is clean, build upward toward the coefficient identity
using `Nat.gcd.induction`; if it is opaque, stop using official `xgcd` and define
target-owned coefficients over the native gcd carrier.

## Durable evidence

The immutable pack is
`/nas3/data/axeyum/autogenesis/reference-packs/609241d91-extended-gcd-novel-dependency-audit-v1/`.
Its mode-`0444` manifest has SHA-256
`a5ea914683ec2bcc626e721d0ec0b7f1daed22867c6814e8a1ba6aaf58d0439a`;
the directory is mode `0555`. No exporter ran, one importer reread occurred,
and no theorem material was rendered.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-novel-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_novel_dependency_audit_result
```
