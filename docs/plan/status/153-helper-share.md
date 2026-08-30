# Lane: helper-share — deduplicating private `creal/*` proof-term builders

<!-- plan-section: lane-status -->

**Census plus five sharing commits landed; the deficiency is real, large, and
only partly addressable while five lanes hold `creal/integral.rs`,
`creal/ivt.rs`, `creal/monotone.rs`, `creal/trig_fn.rs` (`DONE for this slice`,
helper-share, 2026-08-27).** CLAUDE.md names the cost precisely: these are
Rust `fn`s that *construct* proof terms, not kernel `Declaration`s, so a copy
does not create two kernel theorems of one fact — the real cost is ordinary
duplication, where a fix to one copy silently does not reach the others.

**Census** (43 files under `crates/axeyum-lean-kernel/src/creal/` examined,
name-matched on `fn`/`pub(crate) fn`/`pub(super) fn`/`pub fn`, both Rust
naming conventions covered since the match is on the literal `fn` keyword):
**125 distinct `fn` names appear in more than one file**, ranging from 2 to 21
files each (`cmul`/`cneg`/`czero`/`echain` are the widest, but those are
already `pub(super)` in `creal/trig.rs` and imported everywhere — not a
finding, the established-good pattern). Full list is in this session's
transcript; the interesting subset is the private, still-duplicated ones.

**Shared this session** (5 commits, one helper-family each, verified against
the kernel after every one — `creal_prelude_builds` and
`every_creal_declaration_is_checked_and_axiom_free --release` both green,
declaration inventory unchanged, `cargo clippy -D warnings` clean):

Detail moved to [`../notes/153-helper-share.md`](../notes/153-helper-share.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `f6ebbd24a` | Share `equiv_of_sub_equiv_zero`: `deriv_unique.rs` (canonical) ← `exp_fn.rs`. |
| 2026-08-27 | `2f3bb6195` | Share `abs_neg_le`: `uniform_continuity.rs` (canonical) ← `exp_fn.rs`; delete orphaned `double_neg` in `exp_fn.rs`. |
| 2026-08-27 | `0880356d8` | Share `abs_neg_equiv`/`abs_of_nonneg`/`le_sub_of_add_le`: `deriv_unique.rs` (canonical) ← `fermat.rs`; delete orphaned `le_abs_neg_of_le_abs` in `fermat.rs`. |
| 2026-08-27 | `780eb52f1` | Share `add_sub_cancel`: `deriv_unique.rs` (canonical) ← `fermat.rs`; document the two genuinely-different same-named helpers in `convergence.rs`/`uniform_continuity.rs`. |
| 2026-08-27 | `e8a444879` | Share `neg_zero_equiv` (7 copies -> 1): `series.rs` (canonical) ← `derivative.rs`, `fermat.rs`, `geometric.rs`, `mvt.rs`, `power.rs`, `rolle.rs`. |
