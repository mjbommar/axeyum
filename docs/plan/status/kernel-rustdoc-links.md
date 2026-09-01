# Lane: kernel-rustdoc-links — fix the red rustdoc gate in axeyum-lean-kernel

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, kernel-rustdoc-links, 2026-09-01).** Starting:
reproduce the 24 unresolved intra-doc-link errors lane `creal-split` measured
in `crates/axeyum-lean-kernel/src/{nat_prelude,ipc_heyting,ipc_provable}.rs`
under `RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel --no-deps`,
then fix each link doc-comment-only (point at the real item, or demote to
plain code formatting when the item does not exist). Report to follow.

<!-- plan-section: landed-changes -->
