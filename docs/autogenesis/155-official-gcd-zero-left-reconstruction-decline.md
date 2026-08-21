# Official gcd zero-left reconstruction: export-scope decline

Date: 2026-08-21

The frozen source compiled successfully on pinned Lean 4.30 with no compiler
diagnostics. The exporter was invoked without theorem-root selection, however,
so it emitted a 340,033,933-byte complete-module closure. The first independent
import then failed closed at its unchanged two-million-record ceiling:
`RecordLimit { limit: 2000000 }`.

No theorem was admitted, no partial kernel was published, and the second import
did not run. The three exact temporary paths were removed and the original
three-file `s5` baseline is unchanged.

The source proof does not need to change, and increasing the importer limit is
not authorized. The next increment must preregister the exporter's exact
theorem-root syntax and replay the same source into a bounded stream. This
failure is retained because export scope is part of the evidence protocol, not
an incidental performance detail.

The sealed pack is
`/nas3/data/axeyum/autogenesis/reference-packs/96a6a4c34-official-gcd-zero-left-v1`
with manifest SHA-256
`a1f0baf855dfd7c4956693fa002f075263cce4b841997da7b519070440b74d04`.

```sh
python3 scripts/check-autogenesis-official-gcd-zero-left-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_zero_left_reconstruction_result
```
