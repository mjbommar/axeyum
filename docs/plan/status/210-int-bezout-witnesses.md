# Lane: int-bezout-witnesses — computable Bézout witnesses (`Int.gcdA`/`Int.gcdB`)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-bezout-witnesses, 2026-08-28).**
`F:ml430-int-gcd-eq-gcd-ab-63005aef` is **closed**, axiom-free, at Mathlib
v4.30's exact statement `∀ x y : ℤ, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y`.
Six declarations landed in
`crates/axeyum-lean-kernel/src/int_prelude/bezout_witnesses.rs` — three
`Definition`s that return data (`Nat.xgcdAux`, `Nat.gcdA`/`Nat.gcdB`, plus
`Int.gcdA`/`Int.gcdB`) and three `Theorem`s (`Nat.xgcdAux_sound`,
`Nat.gcd_eq_gcd_ab`, `Int.gcd_eq_gcd_ab_witnesses`). Every one measures
`axiom_footprint = 0`.

**The characterization the brief carried was correct.** The pre-existing
`Int.gcd_eq_gcd_ab` is the EXISTENTIAL form
(`∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v`, `int_prelude/gcd.rs:1448`), its
magnitude witnesses come from `Nat.gcd_bezout` — a `Theorem` whose four
naturals sit inside a `Prop` — and its sign handling is a `Prop`-typed
`Or`-elimination. Neither is projectable, so this was a program to write, not
a proof to rearrange. The old name is kept for the existential because
`crt.rs` and `modinv.rs` consume it; the Mathlib-shaped statement is
`Int.gcd_eq_gcd_ab_witnesses`.

**Fuel, and why `m` suffices.** `Nat.xgcdAux` recurses structurally on a fuel
argument (`log.rs`'s device, never `WellFounded`), with a trailing `Bool`
selecting which coefficient to return so ONE recursion carries the pair
without a product type. `Nat.gcdA m n := xgcdAux m m n true`. The invariant
is `m ≤ fuel`, carried as an explicit hypothesis on `Nat.xgcdAux_sound` and
preserved because `succ k ≤ succ f` gives `k ≤ f` while `Nat.mod_lt` gives
`n % succ k < succ k`; at `fuel := m` it discharges to `le_refl`. The bound
constrains the PROOF, not the definition — short of fuel the function still
computes, it just answers for a truncated recursion.

**Three things worth carrying forward.**

Detail moved to [`../notes/210-int-bezout-witnesses.md`](../notes/210-int-bezout-witnesses.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-bezout-witnesses | `Nat.xgcdAux`/`Nat.gcdA`/`Nat.gcdB`/`Int.gcdA`/`Int.gcdB` — extended Euclid as fuel-structural `Definition`s returning data |
| 2026-08-28 | int-bezout-witnesses | `Int.gcd_eq_gcd_ab_witnesses` — Mathlib v4.30's Bézout at named computable witnesses, axiom-free; closes `F:ml430-int-gcd-eq-gcd-ab-63005aef` |
