# Official-gcd balanced-Bézout compilation decline

Date: 2026-08-21

## Result

The accepted private joint quotient/remainder source compiled successfully, but
the one preregistered main-source compilation failed with three independent
source diagnostics. The stop rule therefore fired before export or kernel
import. No source was edited and no compiler retry occurred.

Two diagnostics are notation-shape errors: the theorem statement used `%`,
which elaborated through `HMod.hMod`, while the direct clean computation roots
`Nat.mod.eq_1` and `Nat.mod.eq_2` match `Nat.mod` applications. The third is a
transport-scope error: globally rewriting the quotient equation also rewrote
the remainder nested inside the gcd term, producing a modulo-of-reconstructed-
dividend goal rather than changing only the two coefficient factors.

These are narrow source corrections, not evidence against the existential-
quotient construction. A new increment may state the helper with direct
`Nat.mod` applications and transport the quotient equation only under the two
intended multiplication contexts.

## Execution and cleanup

The non-login SSH shell first exposed that `lake` was absent from `PATH`; no
compiler ran in that shell. The pinned absolute Lean 4.30 `lake` path was then
used for exactly two compiler invocations: one successful support compilation
and one failed main compilation. There were zero exporter invocations, importer
runs, proof-stream reads, or retries after compilation.

All six named temporary paths were removed. The exact three-file pre-existing
`s5` baseline matches byte-for-byte after cleanup. The immutable evidence pack
is:

```text
/nas3/data/axeyum/autogenesis/reference-packs/
  72bbf331d-official-gcd-balanced-bezout-v1/manifest.json
```

Its manifest SHA-256 is
`958d0a12b25c94f667d7ad1418d223c58e37098f31a474168f1fcc4370e16e1c`.
The directory is mode `0555`; every file is mode `0444`.

## Boundary

The successful support compilation is not theorem credit. This decline grants
no quotient witness, balanced Bézout theorem, target specialization,
cancellation, exact Fibonacci submission, receipt, evaluation credit, fact
transition, or ledger write.

## Verification

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_reconstruction_result
```
