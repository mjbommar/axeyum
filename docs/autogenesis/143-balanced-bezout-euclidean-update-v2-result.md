# Parameterized balanced-Bézout update reconstructs cleanly

Date: 2026-08-21

V2 compiled once, exported once, and reconstructed twice in fresh Axeyum
kernels. The two audit reports are byte-identical, and the target's
kernel-derived axiom footprint is empty.

The accepted theorem keeps multiplication associativity and right
distributivity as exact proof parameters. Its direct theorem dependencies are
the seven components the dependency audit already classified as clean. Neither
official `Nat.mul_assoc` nor official `Nat.right_distrib` remains in the
dependency set; `propext`, `funext`, public division equations, and the ring
family are absent as well.

The declaration identity is
`3301a38265badc4cffa6d56c953fa3a5af99b37fc7fecce3cdf053110a536e8b`.
The sealed evidence pack is
`/nas3/data/axeyum/autogenesis/reference-packs/0ffd2dbc9-balanced-bezout-euclidean-update-v2-v1`
with manifest SHA-256
`0b06492d3c6c6a633f67ccdf88e54dc7a6a50dbc5e5c326143cf4d1a5859a949`.
Exact cleanup restored the three-file `s5` baseline.

This grants one parameterized Euclidean-update theorem. It does not yet supply
the two clean leaves. Their identities and target type shapes must be composed
under a separately preregistered gate before the update can enter official gcd
induction.

```sh
python3 scripts/check-autogenesis-balanced-bezout-euclidean-update-result-v2.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_euclidean_update_result_v2
```
