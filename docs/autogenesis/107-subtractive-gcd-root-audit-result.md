# Subtractive gcd root audit result

Date: 2026-08-21

## Result

The official convenience-root shortcut declines. The single pinned export and
single batch importer pass found no empty-footprint theorem among the seven
preregistered roots:

| Roots | Count | Footprint class |
|---|---:|---|
| `Nat.gcd_one_left`, `Nat.gcd_zero_left` | 2 | `Quot.*`, `Quot.sound` |
| the two subtraction roots, the two right roots, and `Nat.gcd_self` | 5 | `Quot.*`, `Quot.sound`, `propext` |

The stream-wide axiom inventory was `Quot.sound` plus `propext`; the kernel's
per-theorem traversal then showed exactly how each selected root reaches that
inventory. No theorem type, value, or proof expression was rendered.

## Consequence

Subtractive Bézout remains mathematically viable, but these seven official
proofs cannot be its trusted foundation. Their direct dependencies form an
exact 17-name frontier. That frontier includes the private gcd equation,
`Nat.gcd_succ`, the two more-general subtraction/multiplication equations,
`Nat.mod_one`, `Nat.mod_self`, and proposition/equality congruence helpers.

The next bounded measurement should classify that exact union before writing a
replacement. If the computational gcd equation and the two general subtraction
equations are empty-footprint, reconstruct only the contaminated wrappers and
resume the division-free proof. If the contamination descends into gcd's
computational core, the honest next layer is the gcd definition/termination
carrier rather than an imported convenience theorem.

No Bézout source was compiled. No support theorem, Fibonacci target, executor,
evaluation, fact, or ledger credit was issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/38e40236f-subtractive-gcd-root-audit-v1/manifest.json`

Its manifest SHA-256 is
`6b03e14eccbbbdf9dbb76750f0f60ba8c045237ba355eea04f436f66cfd39aa0`.

## Verification

```sh
python3 scripts/check-autogenesis-subtractive-gcd-root-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_subtractive_gcd_root_audit_result
```
