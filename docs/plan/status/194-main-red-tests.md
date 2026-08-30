# Lane: main-red-tests — the two tests that had been red on `main`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, main-red-tests, 2026-08-28).** Both failures were
pre-existing on `main`, both reproduced, both diagnosed to a named cause, both
fixed. `cargo test -p axeyum-solver --lib --features full` is **1438 passed, 0
failed** with `RUST_MIN_STACK` unset, and `-p axeyum-bench --test
qfbv_proof_export` is 2/2.

## 1. `monomial_bound` (and three more modules) — the `creal` prelude outgrew the default stack

**It reproduces in `--release`**, so the brief's discriminator fires — but the
requirement is **finite and bounded in both profiles**, which the "fails in
release ⇒ runaway recursion" heuristic does not distinguish. Measured two
independent ways:

| what | debug | release |
| --- | --- | --- |
| `--measure --prelude creal` (smallest power of two) | 16,777,216 | 8,388,608 |
| pinned in `artifacts/kernel-stack-envelope.tsv` (2026-08-26) | 2,097,152 | 131,072 |
| fine bisection of the release test binary | — | aborts at 4,456,448, completes at 4,587,520 |

So the cause is not a false assertion and not a non-terminating term: the
`CReal` development's stack requirement grew **8x in debug and 64x in release
in two days**, past the 2 MiB a `#[test]` thread gets by default.
`scripts/check-kernel-stack-envelope.sh --check --prelude creal` — the gate that
exists precisely to convert this symptom into an explained failure — is **red on
`main`**, and nobody ran it.

The blast radius is wider than the two tests the reporting lane named, because a
stack overflow aborts the whole process and kills the rest of the run. Every
test that builds the constructed reals was affected:
`reconstruct::arithmetic::{monomial_bound, zero_product, product_positivstellensatz,
signature::signature_tests}` and `reconstruct::tests`. Only the first to run
reported.

Fixed at the one place they all funnel through:
`LraReconstructCtx::try_new_over_constructed_reals_reporting` now builds on a
256 MiB worker (16x the measured debug requirement, the workspace's
`DEEP_STACK_BYTES` figure), which also covers the front-door
`try_new_over_constructed_reals` path where an overflow would have aborted a
consumer's process. The one direct `build_creal_prelude` outside that
constructor, in `signature_tests::creal_signature`, uses the same helper.

Detail moved to [`../notes/194-main-red-tests.md`](../notes/194-main-red-tests.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | main-red-tests | `qfbv-proof-export` could not succeed on ANY input since `81361cdd1` made `set-logic` positional; and the `creal` prelude outgrew the 2 MiB default stack (16 MiB debug / 8 MiB release measured, pinned at 2 MiB / 128 KiB) so every constructed-reals test aborted the binary |
