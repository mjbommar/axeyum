# Lane: nat-lor — land `Nat.lor` (bitwise OR) following `Nat.land`'s fuel-recursion pattern

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-lor, 2026-08-28).** Landed `Nat.lor`/
`Nat.lorAux` in `nat_prelude/lor.rs`, following `land.rs`'s structural fuel
recursion (`Nat.rec` on the fuel argument), with two design deviations that do
not transfer unchanged from `Nat.land`:

- **Per-bit combinator**: `max (m%2) (n%2)` via the existing `Nat.ble` +
  `bool_select_nat`, not `a + b - a*b` (avoids a `Nat.sub` height dependency
  and its silent-truncation risk, even though truncation cannot actually
  trigger on bit-restricted inputs) and not a bespoke `Bool.rec` cut (more
  construction for the same result). OR of two `{0,1}` values is not their
  product, so `land`'s `mul` shortcut does not transfer at all.
- **Fuel-exhaustion base case**: `lorAux`'s `fuel = 0` row returns `n`, not
  the constant `0` `landAux` uses. Fuel stays `= m` (unchanged from `land`),
  which stays sound because whenever the outer `Nat.rec` on fuel truly
  reaches `0`, the repeatedly-halved `m`-argument is already `0` too (`m`
  always exceeds the `⌊log₂ m⌋ + 1` halvings needed to exhaust it) — but OR
  has no absorbing zero the way AND does, so the base case must return the
  other operand (`n`), not `0`. This is the part of "the shortcut does not
  transfer" that needed actually working out, not just the per-bit formula.
- **Guard order transferred unchanged**: `n = 0` checked OUTERMOST in
  `lorAux`'s succ case (mirrors `landAux`), and it is load-bearing for the
  same reason: `lor_zero_right`'s induction on `m` closes by `Eq.refl` at
  every step (no induction hypothesis forced), because the outermost
  `bool_select_nat` on `n_is_zero` selects the "return `m`" branch without
  forcing the untaken branch where the real recursive step lives.

Landed 3 boundary/sanity theorems (`lor_zero_left`, `lor_zero_right`,
`lor_three_five`), matching the "two or three boundary lemmas is a complete
success" scope. `lor_three_five = 7` is deliberately the same numeral pair as
`land_three_five = 1`, so the two proof terms differ only in the per-bit
combinator and their results are maximally distinguishing.

Detail moved to [`../notes/219-nat-lor.md`](../notes/219-nat-lor.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-lor | `Nat.lor`/`Nat.lorAux` (fuel recursion, `max`-via-`ble` per-bit step, `n`-returning fuel base case) + 3 boundary theorems in `nat_prelude/lor.rs`; wired into `nat_prelude.rs`; `nat_prelude_tests.rs` coverage + dedicated test + pinned render count `476->481`; 3 new `F:nat-lor-*` facts |
