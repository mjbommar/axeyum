# Lane: int-order-add — the `Int` order/addition family

<!-- plan-section: lane-status -->

**Closed all ten dispatched facts** (`DONE`, int-order-add, 2026-08-29).

## Step 0 finding: one of ten already existed

`Int.add_le_add` (`F:ml430-int-add-le-add-a76ad5ce`) was already declared in
`int_prelude/order.rs::declare_additive_order`, built from the `sub_nat_nat`
difference-witness technique (destructure each `le` hypothesis into an
explicit non-negative gap, re-associate, read the conclusion off the trivial
direction — no `Int.rec` case split). This fact closed as a pure status flip
plus evidence attachment: no new proof was written for it. Confirmed absent
under any other name first via `prelude_theorem_inventory --release
--include-constructed` before concluding the other nine were genuinely new.

## The other nine: `crates/axeyum-lean-kernel/src/int_prelude/order_add.rs`

All nine build as pure algebra on top of three already-derived facts —
`Int.add_le_add`, `Int.add_neg_cancel_right` (`algebra.rs`), and `modeq.rs`'s
private `cancel_neg_add`/`cancel_neg_add_left` (the latter widened from
`fn` to `pub(super)`, the only change outside the new file and
`int_prelude.rs`'s field/dispatch wiring). **No `Int.rec` case split anywhere
in the new file** — this is exactly why the task's "should be cheap"
framing held:

- `Int.add_le_add_left` / `Int.add_le_add_right` — `add_le_add` with a
  `le_refl` on the fixed side.
- `Int.add_le_add_iff_left` / `Int.add_le_add_iff_right` — `mpr` is the
  left/right corollary above; `mp` shifts the hypothesis by the common
  term's negation and collapses with `cancel_neg_add_left` /
  `add_neg_cancel_right`.
- `Int.add_le_add_three` — two applications of `add_le_add`.
- `Int.add_le_iff_le_sub` — `mp`/`mpr` shift by `-b` and collapse with
  `add_neg_cancel_right` / `cancel_neg_add`.
- `Int.add_le_of_le_neg_add`, `Int.add_le_of_le_sub_left`,
  `Int.add_le_of_le_sub_right` — each shifts the hypothesis by `a` (or `b`)
  itself via `add_le_add` and collapses with a small `a + (-a + x) = x`
  identity (`add_cancel_neg_left`, new, the mirror image of
  `cancel_neg_add_left` with `a` and `-a` swapped) or `cancel_neg_add`.

`Int.sub a b := add a (neg b)` is `ReducibilityHint::Regular`
(`sub.rs`), so every statement using `c - b` is stated **folded** (matching
the Mathlib form being mirrored) and proved against the **unfolded**
`add c (neg b)` throughout — `add_declaration`'s own defeq check bridges the
two, per that module's documented convention. No explicit fold/unfold calls
were needed anywhere.

## Mirror-flip check

Detail moved to [`../notes/281-int-order-add.md`](../notes/281-int-order-add.md).

