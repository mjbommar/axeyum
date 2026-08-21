# Pointwise quotient witness reconstructs without assumptions

Date: 2026-08-21

The V4 helper compiled once on pinned Lean 4.30, exported once, and reconstructed
twice in fresh Axeyum kernels. Both audits were byte-identical. The declaration
identity is
`6da60d36575a3aebdfd99ed4f01a5532ef925487e50d48a5d4f4210cf65e0a55`,
and both kernel-derived axiom footprints are empty.

The accepted theorem is deliberately pointwise:

```text
forall m n, 0 < m -> exists q, m * q + Nat.mod n m = n
```

Its direct dependencies contain the private reconstructed division worker,
the two public `Nat.mod` computation equations, concrete equality transport,
and elementary Nat leaves. They contain none of `funext`, `propext`, public
division equations, or Mathlib's ring-normalization family. This confirms the
V3 diagnosis: quotient existence itself was not contaminated; rewriting under
a binder was.

The sealed pack is
`/nas3/data/axeyum/autogenesis/reference-packs/eb061c9bf-mod-quotient-witness-v4-v1`
with manifest SHA-256
`63d81f827241a829fdf8b70616646c23f1519f7b615ac2b9e0ebce2b0c5913a8`.
The directory is mode `0555` and every file is mode `0444`. Exact cleanup
restored the three-entry `s5` baseline.

This grants one quotient-witness result and nothing else. The next independent
gate is an explicit balanced-Bézout Euclidean update over the existing four-Nat
carrier. It must replace `ring` with concrete Nat equality chains before the
generic gcd induction may use it.

```sh
python3 scripts/check-autogenesis-mod-quotient-witness-kernel-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_mod_quotient_witness_kernel_result
```
