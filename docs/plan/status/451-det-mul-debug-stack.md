# Lane: det-mul-debug-stack — the push-blocking debug stack overflow in `det_mat_mul_computes_at_concrete_matrices`

<!-- plan-section: lane-status -->

**WIP, det-mul-debug-stack, 2026-09-03.** `scripts/lane-push.sh` runs
`cargo test --workspace --lib` in DEBUG as an early battery step, and on `main`
`crates/axeyum-lean-kernel/src/rat_prelude/det_mul_tests.rs`
`det_mat_mul_computes_at_concrete_matrices` (added by lane `det-mul-2`,
ADR-1543) aborts with SIGABRT there while passing `--release`. Reproducing,
measuring the debug stack requirement with
`scripts/check-kernel-stack-envelope.sh --measure`, bisecting within the test
(1×1 vs 2×2 instantiation), and fixing by the
[prelude build cost](../../contributor-guide/prelude-build-cost.md) remedies
without weakening ADR-1543's evaluation table.

<!-- plan-section: landed-changes -->

| 2026-09-03 | det-mul-debug-stack | opened: debug-profile stack overflow in the ADR-1543 concrete-matrix evaluation test |
