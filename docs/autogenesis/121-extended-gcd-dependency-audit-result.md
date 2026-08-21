# Extended-gcd direct-dependency audit result

Date: 2026-08-21

## Result

The one preregistered reread classified all twelve direct dependencies of
`Nat.gcd_eq_gcd_ab`:

- eight ordinary equality and arithmetic support roots have empty footprints;
- `eq_self` carries `propext`;
- all three coefficient-core roots are `propext`-bearing;
- `Nat.xgcdAux_val` and the private xgcd invariant also reach the Quotient
  axioms.

Most importantly, `Nat.xgcd_val` has footprint `[propext]` and **zero direct
theorem dependencies**. There is no cleaner imported theorem leaf beneath that
official proof. Its proof-free statement is only

```text
∀ (x y : ℕ), x.xgcd y = (x.gcdA y, x.gcdB y)
```

so a target-owned replacement is plausible, but it requires a separately
preregistered source compilation and kernel measurement.

The other two coefficient roots expose eighteen novel dependencies. The next
audited descent is bounded to those names; it must happen before an explicit
extended-gcd reconstruction can be authorized.

## Durable evidence

The immutable pack is
`/nas3/data/axeyum/autogenesis/reference-packs/609241d91-extended-gcd-dependency-audit-v1/`.
Its mode-`0444` manifest has SHA-256
`a9177779f2ef4adaf35f4d170c7b2a08eaa1c3a5c76de7ffb10bd43f0baeff49`;
the directory is mode `0555`. No exporter ran, the sealed stream was imported
once, and no proof, type, or theorem value was rendered.

## Verification

```sh
python3 scripts/check-autogenesis-extended-gcd-dependency-audit-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_extended_gcd_dependency_audit_result
```
