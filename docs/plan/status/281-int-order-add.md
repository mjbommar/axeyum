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

All ten are theorems in Mathlib's `Int` namespace about the SAME
`Int.add`/`Int.le`/`Int.sub` this kernel already has — no new definition is
introduced by any of them, so the mirror-flip criterion (definition vs.
theorem-about-a-different-definition) is not in play here; these are pure
order/ring corollaries. Confirmed against the pinned Mathlib v4.30.0 source
(commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) via the fact files'
`formal.statement`, which the task noted are faithful quotations of the
pinned extractor.

## Evidence

Each of the ten facts got the same three-row shape:

1. `kernel-Int.<name>` — the kernel's own rendered Pi type (via
   `int_theorem_inventory --release`, matched with `awk -F'\t'` on the
   `kind`/`name`/`type` columns exactly). **Verified discriminating, not
   vacuous**: a one-argument transposition in the expected type string
   flips the check from pass to fail.

   Deliberately **not** `grep -F` with a literal `\t` in the pattern — `-F`
   does no escape interpretation, so a literal backslash-t never matches a
   real tab byte. This is the tab trap CLAUDE.md documents for `grep -E`,
   one layer further into fixed-string mode; `awk`'s `-F` argument does
   interpret `\t`, so it is the safe tool here.
2. `footprint-Int.<name>` — `nat_axiom_inventory --include-constructed
   --require-axiom-free integer` (independently sums the whole `integer`
   prelude's trusted surface and fails nonzero), backed by
   `derived_laws_have_no_axiom_footprint` (the pinned list, now 169 entries,
   recounted with `scripts/recount-pinned-inventory.py`, not incremented by
   hand).
3. `coverage-Int.<name>` — `every_int_declaration_is_checked_and_axiom_free`,
   which derives coverage from `kernel.environment()` directly.

All three checker_commands were run against the committed kernel state
before being written into the fact files, not merely constructed by
analogy. `python3 scripts/validate-facts.py`: 0 errors.

## Checks run (foreground, this session)

- `cargo check -p axeyum-lean-kernel --lib` — clean.
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **49 passed, 0
  failed** (includes `int_prelude_admits_all_declarations`,
  `every_int_declaration_is_checked_and_axiom_free`,
  `derived_laws_have_no_axiom_footprint`; `RUST_MIN_STACK` was not set in
  this shell, so no `env -u` wrapper was needed — confirmed with
  `echo "${RUST_MIN_STACK:-unset}"` before running).
- `cargo fmt --all --check` — clean.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` —
  clean.
- `python3 scripts/check-test-attribute-integrity.py` — 0 findings (no
  `#[test]` was added this session — all nine facts' evidence reuses
  already-existing generic tests plus the new `int_theorem_inventory` /
  `nat_axiom_inventory` example tools, so there was nothing new to check
  for a misplaced attribute).
- Did **not** run the workspace-wide gate (`just check` / `check.sh`), per
  the task's scope.

## Commits

- `fcdbede60` — the nine new theorems (`order_add.rs`), `derived_laws`
  recount 160 → 169, `cancel_neg_add_left` widened to `pub(super)`.
- `43d56a6d9` — all ten facts: evidence attached, `epistemic_status` →
  `proved`.

## Remaining work in this family

None dispatched. If more `Int` order/add corollaries surface later,
`add_cancel_neg_left` (new, `order_add.rs`) and the existing
`cancel_neg_add`/`cancel_neg_add_left` (`modeq.rs`, now `pub(super)`) are
the reusable pieces — check for them before re-deriving.
