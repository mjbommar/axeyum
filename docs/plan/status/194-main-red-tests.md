# Lane: main-red-tests — diagnose the two tests that have been red on `main`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, main-red-tests, 2026-08-28).** Two pre-existing
failures on `main`, both reported by a sibling lane and confirmed not theirs.

1. `reconstruct::arithmetic::monomial_bound::tests::the_refutation_kernel_checks_over_the_constructed_reals`
   — stack overflow. Diagnosis in progress; `--release` is the discriminator.
2. `axeyum-bench --test qfbv_proof_export` (both tests) — **root cause found by
   reading, before any build.** `crates/axeyum-bench/src/bin/qfbv-proof-export.rs:53`
   refuses any script containing a `ScriptCommand` other than `Assert` or
   `CheckSat`. Commit `81361cdd1` (2026-08-21, "a command is answered or says
   `unsupported` — never dropped") made `set-logic` and `set-option` **positional**
   `ScriptCommand`s. The exporter landed 2026-07-19 (`ba9ff7c6c`), before that.
   So every script that satisfies the exporter's own `set-logic QF_BV`
   requirement (checked ten lines earlier) is then rejected by its flatness
   check: the binary cannot succeed on any input at all.

<!-- plan-section: landed-changes -->

| 2026-08-28 | main-red-tests | in progress |
