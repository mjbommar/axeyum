# Official-kernel balanced-Bézout composition decline

Date: 2026-08-21

The exact full-gated driver was built once. Its first five-stream invocation
successfully composed the zero-left leaf, successor leaf, and modulo adapter,
then successfully specialized both the modulo bound and closed successor.

The next operation failed closed before any balanced-Bézout submission:

```text
UnsupportedMissingDeclaration { name: "Acc", kind: "recursive-inductive" }
```

The generic theorem's dependency closure contains the official recursive `Acc`
package, while the chosen r082-based target does not. Axeyum correctly refuses
to synthesize an unsupported missing recursive inductive during theorem-slice
composition. The second invocation was skipped, no partial kernel was
published, and no closed or downstream credit is due.

The next increment reverses the composition direction: preserve the already
complete generic theorem kernel as the base and add only `Nat.mod_lt`, the
modulo adapter, and the two accepted gcd roots. That keeps `Acc` in place and
avoids asking the composition boundary to manufacture it.

The sealed pack is
`/nas3/data/axeyum/autogenesis/reference-packs/9ec4bcfa1-official-gcd-balanced-bezout-official-kernel-v1`
with manifest SHA-256
`6c415e21f6d0816cf59b4fcd4f576d4259e0be0dae9323849ba187fe3a5f69c6`.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-official-kernel-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_official_kernel_result
```
