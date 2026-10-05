# Lane: evt-r2-gap — close the labeled `evtLinear` uniform-continuity gap in EVT row 2

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, evt-r2-gap, 2026-08-28).** The one labeled gap in
`creal/extreme_value.rs` (`evtLinear v` uniformly continuous — asserted, not
proved) is closed. All four pieces landed and are kernel-checked:

1. `CReal.abs_bound_of_self : ∀ x, le (abs x) (mag_bound (bound x))` —
   promoted from a private `fn` in `creal/uniform_continuity.rs` (unreachable
   outside that file) to a `CRealPrelude` field, closed over a fresh `fvar`.
   The sole prior call site (inside `declare_bounded_of_uniformly_continuous`)
   now calls `d.lemma(p.abs_bound_of_self, &[f_a])` instead of rebuilding the
   proof inline. Makes `BoundedOn` trivial for every constant function on
   every interval — not just `evtLinear`'s.
2. `CReal.bounded_on_id_zero_one : BoundedOn (fun r => r) zero one 0` —
   bridges `one` to `mag_bound 0` via `rat_unit_eq_one`
   (`Eq Rat (natDivSucc 1 0) Rat.one`, lifted across `ofRat`), then applies
   `bounded_on_id_unit` directly rather than re-deriving its magnitude
   argument (~35 lines, shorter than the ~60-line route the module doc had
   sketched — see "what I found wrong" below).
3. `CReal.evtLinear_uniformly_continuous : ∀ v, UniformlyContinuousOn
   (evtLinear v) zero one` — `uniformly_continuous_mul` at `F := id`,
   `G := fun _ => v`, both `BoundedOn` arguments discharged by (1) and (2).
   Pure assembly, no new algebra.
4. Module doc in `creal/extreme_value.rs` updated: the "LABELED GAP" section
   is now "CLOSED", and the `evtLinear` field doc comment in `creal.rs` no
   longer says "asserted, not proved".

**What I found wrong in the module doc (now corrected):** it predicted the
`[0,1]` `BoundedOn` case would need `max_le` on `abs`'s two branches plus
`add_le_add` against `le_refl (neg z)`, ~60 lines, built from scratch. The
much cheaper route — transport `hzb : le z one` to `le z (mag_bound 0)` via
the `rat_unit_eq_one` bridge, then apply `bounded_on_id_unit` DIRECTLY at
the transported hypothesis — was available and ~35 lines. Worth knowing for
the next lane that estimates a route by "build from primitives" without
checking whether an existing sibling theorem can just be reused.

**Not attempted / out of scope:** no change to `evt_attained_max_decides_sign`
itself (it never needed continuity as a hypothesis — the gap was purely the
bridge sentence connecting `evtLinear` to classical EVT's hypothesis class).

<!-- plan-section: landed-changes -->

| 2026-08-28 | evt-r2-gap | Closed EVT row-2's labeled gap: promoted `abs_bound_of_self`, added `bounded_on_id_zero_one` and `evtLinear_uniformly_continuous` (all kernel-checked) |
