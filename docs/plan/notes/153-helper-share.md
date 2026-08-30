# Notes: 153-helper-share

Detail moved out of [`../status/153-helper-share.md`](../status/153-helper-share.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
