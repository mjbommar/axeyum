# Lane: allowlist-clippy — trusted-substitution allowlist coverage + workspace clippy cleanup

<!-- plan-section: lane-status -->

**Task 1 `DONE` (2026-08-27), 0 of 15 facts closed — a measured negative
result, not a failure.** Brief: extend `trusted_substitution`/
`nat_order_substitution`'s allowlist to cover `Nat.mod_lt`/`eq_self` (doc
294's estimate of the remaining gap for doc 292's 15 `Nat.Coprime`
`TrustedDeclaration` declines) and re-run the real failing exports.

Measured, not estimated, via a standalone NDJSON decoder against doc 292's
own s5 exports plus the real `statement_goal_record` binary: doc 294's "two
names" estimate undercounts the real closure. The smallest representative
fact needs **15** additional theorem-kind names beyond existing coverage,
not 2 — 7 are generic `WellFounded.fix`/eager-fixpoint internals (a
different, larger construction class `nat_order_substitution`'s technique
doesn't cover), the rest are ordinary order lemmas needing a `Nat.beq`
primitive that module doesn't yet discover. `eq_self` independently needs
`propext`, which this kernel deliberately excludes (intuitionistic design,
`prelude.rs:61`) — architecturally permanent, not deferred engineering.

**Split of the 15**: 1 permanent (`Quot`, hard rule, unchanged from doc
294), 5 permanent (need `propext`), 9 deferred (need the WF-recursion
cascade — real, doable, substantial future engineering, not attempted here
per the brief's own stop condition). 0 closed. No changes made to any of
the four substitution modules — nothing was safely addable within a
reviewed scope. Guard mutation test reproduced doc 294's result exactly (3
tests red with the whole-stream `matches!` guard neutered; restored clean).
Full writeup: `docs/autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md`.

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
