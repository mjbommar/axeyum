# Notes: allowlist-clippy

Detail moved out of [`../status/allowlist-clippy.md`](../status/allowlist-clippy.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Task 2 `DONE` (2026-08-27).** `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` (and `--all-features`) now both exit 0. 25
`error:` lines / 23 distinct issues before this lane (confirmed the earlier
"~23-25" report was real, not stale): 12 `doc_lazy_continuation`
(`uniform_convergence.rs` x11, `integral.rs` x1), 7 `unused_mut`
(`creal_model_tests.rs`), 1 `used_underscore_binding` (`integral.rs`), 1
`items_after_statements` (`cas_bridge_tests.rs`), 1 `items_after_test_module`
(`convergence.rs`), 1 `map_unwrap_or` (`complex_tests.rs`). Fixing the first
two surfaced two more in `examples/kernel_declaration_projection.rs`
(`collapsible_if`, then `too_many_lines` once the allow's own lines pushed
a 100-line function to 101) — fixed the same way. All fixes are doc-comment
indentation, `mut` removal, or a scoped `#[allow]` with a one-line reason;
`git diff --stat` across all 7 touched files is 36 insertions / 19
deletions, entirely mechanical (verified by reading every hunk). No proof
term, declaration, or logic changed. `integral.rs`'s doc fix and
`convergence.rs`'s `#[allow(clippy::items_after_test_module)]` are in
FTC-lane-owned files — both are single-line, non-restructuring insertions
(doc-comment-only for `integral.rs`; a scoped allow, not a code move, for
`convergence.rs`), matching the brief's own precedent for
`large_stack_arrays`. Reran `cargo test -p axeyum-lean-kernel --lib` on
every touched test (`creal_model_tests` x7, `complex_tests::
the_ring_calculus_refuses_a_false_identity`,
`integral::common_refinement_tests::
common_refinement_proof_rejected_at_wrong_type`) — all pass.

## Landed changes

| commit | what |
|---|---|
| (this lane, Task 1) | doc 295 (measurement); no source changes |
| (this lane, Task 2) | mechanical clippy fixes, 7 files, doc/mut/allow only |
