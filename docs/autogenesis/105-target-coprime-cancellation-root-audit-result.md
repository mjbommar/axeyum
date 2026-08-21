# Target coprime-cancellation root audit result

Date: 2026-08-21

## Result

The narrow target-side shortcut declines. The single pinned export and importer
pass found:

| Root | Footprint | Decision |
|---|---|---|
| `Nat.Coprime.eq_1` | empty | usable definition equation |
| `Nat.Coprime.coprime_dvd_left` | `Quot.*`, `Quot.sound`, `propext` | decline |
| `Nat.Coprime.dvd_of_dvd_mul_left` | `Quot.*`, `Quot.sound`, `propext` | decline |

Importing the two convenience theorems would enlarge the trusted base beyond
the existing public-equation seam. Statement availability therefore does not
make this an acceptable adapter.

## Consequence

The exact relationship between `Nat.Coprime` and `gcd = 1` is clean, so it
remains useful for a future independently authored proof. The divisibility
inheritance and cancellation steps must be reconstructed locally, or derived
through a different subtractive gcd route. The broader bottom-up Euclidean work
remains live; this result merely closes the tempting target shortcut.

No proof term or theorem value was rendered. No support theorem, Fibonacci
target, evaluation, fact, or ledger credit was issued.

## Verification

```sh
python3 scripts/check-autogenesis-coprime-target-cancellation-root-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_coprime_target_cancellation_root_audit_result
```
