# Official gcd zero-left root export result

Date: 2026-08-21

The unchanged Lean 4.30 source compiled once. Supplying the exact theorem root
reduced the export from 340,033,933 bytes to 509,474 bytes, below the frozen
two-megabyte ceiling without increasing the importer's two-million-record
limit.

Two fresh Axeyum kernel imports produced byte-identical audits. The theorem
`Axeyum.Autogenesis.nat_gcd_zero_left` has an empty axiom footprint and exactly
one direct theorem dependency:
`Axeyum.Autogenesis.gcdModel_zero_left`. The forbidden official zero-left,
generated fix equation, `funext`, and `propext` dependencies are absent. No
proof term, theorem type, or theorem value was rendered.

The exact three temporary `s5` paths were removed and its original three-file
baseline was restored. The evidence pack is sealed read-only at
`/nas3/data/axeyum/autogenesis/reference-packs/0a73f8458-official-gcd-zero-left-root-v1`
with manifest SHA-256
`f7d01b5c782b098fce84d8ce342d53c7da70bc2fe8d59864e0d44d04c095ff0e`.

This closes only the official-representation zero-left gcd computation leaf.
The successor equation must be reconstructed independently before either leaf
can be composed into the accepted generic balanced-Bezout theorem.

```sh
python3 scripts/check-autogenesis-official-gcd-zero-left-root-export-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_zero_left_root_export_result
```
