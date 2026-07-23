# Lean complete-parity current-main integration R4 result

Date: 2026-07-23

Status: **detached-mount fixture corrected and validated; no process or parity credit**

Plan: [R4 plan](lean-complete-parity-main-integration-r4-plan-2026-07-23.md)

## 1. Result

R4 fixes the remaining checkout-root-sensitive store-validator test fixture
found while verifying the merged portability lane from a detached worktree
below `/tmp`. The parent portability integration was merged as `6ad45d44`; R4
was based on then-current `main` at `5b42a0ef`.

The production validator was correct. Its retained descriptor requires
`class_root` to remain within the descriptor's observed `mount.mount_point`.
The test's literal `/different/checkout/axeyum` accidentally satisfied that
invariant only on checkouts whose observed mount was `/`. In the detached
checkout, the observed mount was `/tmp`, so the literal path was correctly
rejected.

Commit `77423b0a` now derives the accepted alternate root beneath the retained
descriptor's own mount point. It also adds a fail-closed control with
`class_root=/different/checkout/axeyum` and
`mount_point=/observed/mount`, which is rejected with the exact diagnostic
`storage class root is outside its observed mount`. No production validator
was relaxed.

## 2. Commits

- `5cf8348f` preregisters the detached-mount correction and nonclaims.
- `77423b0a` corrects the fixture and adds the outside-mount rejection.
- `a18bc448` binds the changed test bytes in the generated complete-parity
  authority.

Every commit is path-scoped and carries the required co-author trailer.

## 3. Validation

All validation below ran from
`/tmp/axeyum-lean-portability-main-verify.LXhX14`, where the defect had been
reproduced:

- the focused store regression passes;
- the combined process, store, and acceptance suites pass: 62 tests, with one
  intentional skip;
- the exact process result remains `controls=8`, `files=40`,
  `real_outcomes=0`, `paired_cells=0`, `parity_credit=0`;
- the exact store result remains `classes=2`, `kill_cells=16`,
  `projection_equal=16`, `real_outcomes=0`, `paired_cells=0`,
  `parity_credit=0`;
- the exact acceptance result remains `controls=2`, `u2_cases=0`,
  `official_outcomes=0`, `axeyum_outcomes=0`, `paired_cells=0`,
  `performance_rows=0`, `parity_credit=0`;
- `just parity-docs` passes, including
  `LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false`;
- `just links` passes.

After committing the result, the focused 24-test store suite, full
`just parity-docs`, and `just links` were repeated successfully from a second
fresh detached checkout at `/tmp/axeyum-lean-r4-fresh.UfEUKG` on `1efdfbb7`.
The checkout was clean after the gates and was then removed.

`cargo fmt --all --check` remains red on unrelated pre-existing Rust files,
including `crates/axeyum-bench/examples/audit_dominance.rs` and multiple
`crates/axeyum-cas` sources. R4 owns no Rust files and does not rewrite that
concurrent work.

## 4. Nonclaims

R4 performs no external Lean, Axeyum, SMT-solver, network, or retained-evidence
execution. It changes no accepted outcome, authority projection, denominator,
or evidence identity. Complete Lean 4 parity remains open: the terminal
contract is explicitly false and all paired-cell credit remains zero.
