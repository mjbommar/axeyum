# Official gcd successor root export result

Date: 2026-08-21

The unchanged Lean 4.30 source compiled once and the exact successor root
exported to a 511,748-byte stream. Two fresh Axeyum kernel imports produced
byte-identical audits. `Axeyum.Autogenesis.nat_gcd_succ` has an empty axiom
footprint and exactly one direct theorem dependency:
`Axeyum.Autogenesis.gcdModel_succ`.

This is specifically the official Mathlib `WellFounded` representation needed
by the generic balanced-Bezout stream. It does not double-count the earlier
mathematically accepted successor theorem in the incompatible native-support
kernel. Together with the accepted zero-left result, both computation leaves
needed for official-kernel composition are now independently available.

The three temporary `s5` paths were removed and its exact baseline restored.
The read-only evidence pack is
`/nas3/data/axeyum/autogenesis/reference-packs/dfcff00d1-official-gcd-succ-root-v1`
with manifest SHA-256
`c1ebf421a26764d7796932c49ebbc6d1c3a889a665e6d4830a28a78b97f83a2a`.

Closed balanced-Bezout remains uncredited. Its next attempt must be separately
preregistered and compose these two exact streams with the accepted generic
theorem inside the official kernel.

```sh
python3 scripts/check-autogenesis-official-gcd-succ-root-export-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_succ_root_export_result
```
