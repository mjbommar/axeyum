# Lane: solver-rustdoc-links — fix the red rustdoc gate in axeyum-solver and axeyum-lean-import

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, solver-rustdoc-links, 2026-09-01).** Fixed all 7
`error:` lines that `kernel-rustdoc-links` and `cas-rustdoc-links` reported
out of scope, closing out the workspace rustdoc gate they left red —
confirmed by reproducing the failure first (exit 101, 7 `error:` lines,
matching their reports exactly) and re-running the identical command after
the edits (exit 0, 0 errors). One link named a real public item and got a
qualified path: `[`NeedsLeanCheck`]` in `thin_adapter.rs` is the enum variant
`PreLeanStage::NeedsLeanCheck`, and `[`Kernel::render_lean_module_compact`]`
in `diophantine.rs` needed the fully-qualified
`axeyum_lean_kernel::Kernel::render_lean_module_compact` (the file only
imports `BinderInfo`/`ExprId` from that crate, and other files in this same
crate already use this exact qualified-path pattern). The other two links in
`proof.rs` (`finish_unsat_proof_outcome_with_check_budget`,
`qf_bv_cnf_encoding`) name genuinely private free functions with no public
re-export, so both were demoted to plain code-formatted text, same as the
prior two lanes' fixes. Every fix is doc-comment-only: no lint disable, no
`allow`, no visibility change, no deleted doc comment. Touched files:
`crates/axeyum-lean-import/src/thin_adapter.rs`,
`crates/axeyum-solver/src/proof.rs`,
`crates/axeyum-solver/src/int_reconstruct/diophantine.rs`. `rustfmt
--edition 2024` on all three: only the intended-edit lines changed, no other
diff.

Re-ran the full command: `RUSTDOCFLAGS="-D warnings"
scripts/cargo-serialized.sh doc --workspace --all-features --no-deps` — exit
0, 0 `error:` lines (was exit 101, 7 error lines). `--all-features` built
cleanly, including the `z3` feature, so no C-toolchain fallback was needed.
The workspace rustdoc gate is now green end to end.

<!-- plan-section: landed-changes -->

| 2026-09-01 | solver-rustdoc-links | Fixed the last 7 broken rustdoc intra-doc-links in `crates/axeyum-lean-import/src/thin_adapter.rs` and `crates/axeyum-solver/src/{proof,int_reconstruct/diophantine}.rs`; `cargo doc --workspace --all-features --no-deps` under `RUSTDOCFLAGS="-D warnings"` now exits 0 workspace-wide (was exit 101, 7 error lines — the last two crates left red by `kernel-rustdoc-links` and `cas-rustdoc-links`). |
