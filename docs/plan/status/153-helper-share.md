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

- `equiv_of_sub_equiv_zero` — `deriv_unique.rs` (now `pub(super)`) ←
  `exp_fn.rs`. (`monotone.rs`/`trig_fn.rs` copies untouched, live lanes.)
- `abs_neg_le` — `uniform_continuity.rs` (now `pub(super)`) ← `exp_fn.rs`.
  Orphaned `exp_fn.rs`'s private `double_neg`; deleted as dead code.
  (`monotone.rs` has a *different* `abs_neg_le` — single-arg, proves
  `le(abs(neg t))(abs t)`, not this family's `le(abs w) q -> le(abs(neg w))
  q` — confirmed by diff, correctly left alone; `trig_fn.rs`'s copy of THIS
  shape is untouched, live lane.)
- `abs_neg_equiv` / `abs_of_nonneg` / `le_sub_of_add_le` — `deriv_unique.rs`
  (now `pub(super)`) ← `fermat.rs`. Orphaned `fermat.rs`'s private
  `le_abs_neg_of_le_abs`; deleted as dead code (itself a 3-file duplicate —
  `deriv_unique.rs`, `derivative.rs`, `fermat.rs` — noted for a future
  slice, not chased here).
- `add_sub_cancel` — `deriv_unique.rs` (now `pub(super)`) ← `fermat.rs`. This
  name is a **collision across three genuinely different helpers**, not one
  duplicate group: `convergence.rs`'s is over `Rat` and returns a pair;
  `uniform_continuity.rs`'s takes arguments in the other order and proves a
  different statement. Only the `deriv_unique.rs`/`fermat.rs` pair (byte-
  identical) was merged; the other two are noted in the shared copy's own doc
  comment so the next reader does not mistake them for more copies.
- `neg_zero_equiv` — the widest win: **7 private copies**, all byte-identical
  modulo comments and one no-op wrapper substitution (`esymm(d,p,a,b,h)` is
  literally `d.lemma(p.equiv_symm,&[a,b,h])`, confirmed by reading `esymm`'s
  body). `series.rs` (the traced origin, per every other copy's own doc
  comment) is now `pub(super)`; `derivative.rs`, `fermat.rs`, `geometric.rs`,
  `mvt.rs`, `power.rs`, `rolle.rs` all import it instead of keeping their
  own. `uniform_convergence.rs` has an eighth same-named fn that is a
  genuinely different construction (raw `const_app`/`equiv_trans`, not
  `czero`/`cneg`/`cadd`/`echain`) — confirmed by diff, left alone.

**Not attempted this slice, and why**: the remaining ~115 duplicate-name
groups from the census, most because (a) at least one copy lives in the four
excluded live-lane files and sharing the rest is only a partial win worth
sizing separately, or (b) time budget — this slice prioritized the three
families CLAUDE.md's own retrospective named plus `add_sub_cancel` (found
while diffing `abs_neg_equiv`'s neighbours) and `neg_zero_equiv` (found while
diffing `neg_zero_equiv`'s siblings, the single widest win in the census).
`le_abs_neg_of_le_abs` (3 editable-file duplicate, orphaned but not yet
removed from `derivative.rs`) is a concrete next task.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `f6ebbd24a` | Share `equiv_of_sub_equiv_zero`: `deriv_unique.rs` (canonical) ← `exp_fn.rs`. |
| 2026-08-27 | `2f3bb6195` | Share `abs_neg_le`: `uniform_continuity.rs` (canonical) ← `exp_fn.rs`; delete orphaned `double_neg` in `exp_fn.rs`. |
| 2026-08-27 | `0880356d8` | Share `abs_neg_equiv`/`abs_of_nonneg`/`le_sub_of_add_le`: `deriv_unique.rs` (canonical) ← `fermat.rs`; delete orphaned `le_abs_neg_of_le_abs` in `fermat.rs`. |
| 2026-08-27 | `780eb52f1` | Share `add_sub_cancel`: `deriv_unique.rs` (canonical) ← `fermat.rs`; document the two genuinely-different same-named helpers in `convergence.rs`/`uniform_continuity.rs`. |
| 2026-08-27 | `e8a444879` | Share `neg_zero_equiv` (7 copies -> 1): `series.rs` (canonical) ← `derivative.rs`, `fermat.rs`, `geometric.rs`, `mvt.rs`, `power.rs`, `rolle.rs`. |
