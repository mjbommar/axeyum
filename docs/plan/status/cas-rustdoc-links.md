# Lane: cas-rustdoc-links — fix the red rustdoc gate in axeyum-cas

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, cas-rustdoc-links, 2026-09-01).** Fixed all 8
`error:` lines (7 broken-link errors + the summary line) that made
`RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-cas --no-deps` fail —
confirmed by reproducing the failure first (exit 101, matched the count
`kernel-rustdoc-links` reported) and re-running the identical command after
the edits (exit 0, 0 errors). All six broken links name genuinely private
items with no public re-export (`checker_derivative`, `checker_shift_by` in
`inverse.rs`; `certifies_hermite_shape`, `certifies_smith_shape` in
`normalforms.rs`; `rational_root_candidates`, `MAX_ABS_INT_COEFF`,
`MAX_CANDIDATES` in `rationality.rs`) — every one demoted to plain
code-formatted text (`` `name` `` instead of `` [`name`] ``), doc-comment-only,
no visibility or code change. `rustfmt --edition 2024` on all three touched
files: no diff beyond the intended edits.

Also ran `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features
--no-deps` once, report-only, no fix: exit 101, 7 `error:` lines, all in
`crates/axeyum-lean-import` (`thin_adapter.rs`, unresolved link to
`NeedsLeanCheck`) and `crates/axeyum-solver` (`proof.rs`,
private-intra-doc-links to `finish_unsat_proof_outcome_with_check_budget`
and `qf_bv_cnf_encoding`; `int_reconstruct/diophantine.rs`, unresolved link
to `Kernel::render_lean_module_compact`) — confirmed `axeyum-cas` itself is
clean in this run. Out of this lane's scope, not fixed here.

<!-- plan-section: landed-changes -->

| 2026-09-01 | cas-rustdoc-links | Fixed all 6 broken rustdoc intra-doc-links in `crates/axeyum-cas/src/{inverse,normalforms,rationality}.rs`; `cargo doc -p axeyum-cas --no-deps` under `RUSTDOCFLAGS="-D warnings"` now exits 0 (was exit 101, 8 error lines). Workspace-wide doc build still red: 7 error lines in `axeyum-lean-import` and `axeyum-solver` (out of scope, reported not fixed). |
