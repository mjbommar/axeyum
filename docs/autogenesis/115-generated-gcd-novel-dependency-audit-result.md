# Generated gcd novel-dependency audit result

Date: 2026-08-21

## Result

The final three-root measurement cleanly isolates the official gcd seam:

| Dependency | Footprint |
|---|---|
| `WellFounded.Nat.fix_eq` | `Quot.*`, `Quot.sound` |
| private gcd termination proof | empty |
| generated `PSigma` argument pusher | empty |

The generic well-founded equation theorem is the sole assumption carrier. The
gcd-specific decrease proof—built from `Nat.mod_lt` and positivity—and the
compiler-generated argument transport are both clean.

## Consequence

A bounded reconstruction attempt is now justified, but not yet credited. It
must derive the needed official gcd equation without `WellFounded.Nat.fix_eq`
or any quotient axiom, while retaining only the measured empty generated
helpers. If the official definition remains opaque to such a proof, the route
must decline and move to an explicit target-owned gcd bridge.

No reconstruction ran in this increment and no theorem or ledger credit was
issued.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/38e40236f-generated-gcd-novel-dependency-audit-v1/manifest.json`

Its manifest SHA-256 is
`911879361c1dabffde75aa997fefb58bd72d7f983c281faf1ca33cb9d955febd`.

## Verification

```sh
python3 scripts/check-autogenesis-generated-gcd-novel-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_generated_gcd_novel_dependency_audit_result
```
