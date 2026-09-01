# Lane: cas-rustdoc-links — fix the red rustdoc gate in axeyum-cas

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, cas-rustdoc-links, 2026-09-01).** Picking up
where `kernel-rustdoc-links` (merged as `1606482e1`) left off: the
workspace-wide `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
--all-features --no-deps` run it reported found 8 remaining `error:` lines,
all in `crates/axeyum-cas` (`inverse.rs`, `normalforms.rs`,
`rationality.rs`) — same defect class, public doc comments linking to
private items. Reproducing and fixing now, doc-comment-only, following the
prior lane's pattern (real public item -> `crate::`-rooted path; private
item -> demote to plain code formatting).

<!-- plan-section: landed-changes -->

| 2026-09-01 | cas-rustdoc-links | WIP: reproducing the 8 rustdoc errors in `crates/axeyum-cas` before fixing. |
