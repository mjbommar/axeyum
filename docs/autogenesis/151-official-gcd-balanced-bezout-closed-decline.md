# Closed official-gcd balanced-Bézout specialization decline

Date: 2026-08-21

The new dependency-bound specialization mode compiled, rebuilt the accepted
target-owned gcd leaves, and then declined before submitting the final theorem.
Composing the accepted generic balanced-Bézout stream into that target kernel
encountered an exact type-shape mismatch at `WellFounded.fix`:

- generic-stream shape:
  `f45b230503d6ddc03c61714008f6165dd055ff995d927507fc6d7aaffcf6afd6`;
- target-support shape:
  `0c2e9552a1056133fbd4e6a318344cfb1310468f7d2113efb37ebba0bf6ef32c`.

No proof, theorem type, or theorem value was rendered. No final specialization
was submitted, no partial kernel was published, and the zero-retry ceiling
ended the increment after its first complete invocation. The planned second
reproduction therefore did not run.

This is a representation seam rather than a failed Bézout argument. The next
increment must compare the two `WellFounded.fix` declarations and their
dependency closures without proof rendering. It may then choose an explicit
translation or target-side reconstruction; this decline authorizes neither.

The sealed evidence pack is
`/nas3/data/axeyum/autogenesis/reference-packs/0e23382f8-official-gcd-balanced-bezout-closed-v1`
with manifest SHA-256
`c136a95253f6259e5faed9f10ffa9c0e475f5f5be85c7c3c7a57d5efcaa44d7a`.
The pack also retains the exact executed Rust source; the repository version
adds only a post-run Clippy annotation.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-closed-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_closed_result
```
