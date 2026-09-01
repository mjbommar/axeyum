# Lane: kernel-rustdoc-links — fix the red rustdoc gate in axeyum-lean-kernel

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, kernel-rustdoc-links, 2026-09-01).** Fixed all 23
broken intra-doc-links (24 `error:` lines including the summary) that made
`RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel --no-deps` fail —
confirmed by reproducing the failure first (exit 101, 24 `error:` lines) and
re-running the identical command after the edits (exit 0, 0 errors). Every
fix is doc-comment-only: two real public items (`NatPrelude`, `NatOps`'s
trait methods, both re-exported at the crate root) got an explicit
`crate::`-rooted path; every other link named a `pub(super)`/private
free function, a private submodule (`ops`, `parity`, `matrix_n`,
`rec_agreement`), or a Lean-level name with no Rust item at all
(`Formula`, `FormulaList`) — those were demoted to plain code-formatted text
since fixing them into a real link would need a visibility/code change, out
of scope for a doc-comment-only fix. Touched files:
`nat_prelude.rs`, `ipc_heyting.rs`, `ipc_provable.rs`, `rat_prelude.rs` (the
last two beyond the three files the initial repro named — `rat_prelude.rs`
carried 2 of the 23 broken links, discovered during reproduction).
`rustfmt --edition 2024` on all four touched files: no diff, already clean.

Also ran `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features
--no-deps` once, report-only, no fix: exit 101, 8 `error:` lines, all in
`crates/axeyum-cas` (`inverse.rs`, `normalforms.rs`, `rationality.rs`) —
same defect class (public docs linking to private items), out of this
lane's scope. Not fixed here.

<!-- plan-section: landed-changes -->

| 2026-09-01 | kernel-rustdoc-links | Fixed all 23 broken rustdoc intra-doc-links in `crates/axeyum-lean-kernel/src/{nat_prelude,ipc_heyting,ipc_provable,rat_prelude}.rs`; `cargo doc -p axeyum-lean-kernel --no-deps` under `RUSTDOCFLAGS="-D warnings"` now exits 0 (was exit 101, 24 error lines). Workspace-wide doc build still red: 8 errors in `axeyum-cas` (out of scope, reported not fixed). |
