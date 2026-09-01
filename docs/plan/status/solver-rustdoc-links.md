# Lane: solver-rustdoc-links — fix the red rustdoc gate in axeyum-solver and axeyum-lean-import

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, solver-rustdoc-links, 2026-09-01).** Starting:
reproduce the 7 remaining `error:` lines that `kernel-rustdoc-links` and
`cas-rustdoc-links` reported out of scope —
`crates/axeyum-lean-import/src/thin_adapter.rs:39` (unresolved link to
`NeedsLeanCheck`), `crates/axeyum-solver/src/proof.rs:297,306,307`
(private-intra-doc-links to `finish_unsat_proof_outcome_with_check_budget`
and `qf_bv_cnf_encoding`), and
`crates/axeyum-solver/src/int_reconstruct/diophantine.rs:64` (unresolved
link to `Kernel::render_lean_module_compact`) — under
`RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps`,
then fix each link doc-comment-only (point at the real item if public, or
demote to plain code formatting if private/nonexistent). Report to follow.

<!-- plan-section: landed-changes -->
