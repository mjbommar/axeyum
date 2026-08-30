# Lane: nat-bitwise-2 — land `Nat.land` (bitwise AND), directly, not through `Nat.bitwise`

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-bitwise-2, 2026-08-28).**

The frontier (per the prior `207-nat-bitwise` lane, which landed `Nat.bit`)
still had `Nat.bitwise`, `Nat.land`, `Nat.lor`, `Nat.ldiff`, `Nat.bits`
undeclared, blocking the `F:ml430-nat-bitwise-*`/`F:ml430-nat-land-*`/
`F:ml430-nat-lor-*`/`F:ml430-nat-ldiff-*` mirror facts. Per the brief, this
lane's target was one complete definition with boundary lemmas.

**`Nat.land` landed directly, NOT through a general `Nat.bitwise`.** Mathlib
routes `Nat.land := bitwise and`, and `Nat.bitwise` needs a `Bool -> Bool ->
Bool` function argument threaded through mismatched-length base cases
(`m=0`: `if f false true then n else 0`; `n=0`: `if f true false then m else
0`) — substantially more construction than a single lane's scope. `Nat.land`
needs none of that: each bit's AND is the `Nat` **product** of two values
already in `{0, 1}` (`Nat.mod _ 2`), so the recursive step is pure
arithmetic with no `Bool`/`cond` combinator at all — simpler than `Nat.bit`
needed to be.

**The fuel device WAS needed, and it is the exact shape `Nat.logAux`/
`Nat.testBitAux`/`Nat.sizeAux` already use**: structural `Nat.rec` on a fuel
argument, carrying `m`/`n` through and halving them (`Nat.div _ 2`) at each
step:

```
Nat.landAux 0        m n ≡ 0
Nat.landAux (succ f) m n ≡
  if n = 0 then 0
  else if m = 0 then 0
  else 2 * landAux f (m / 2) (n / 2) + (m % 2) * (n % 2)
Nat.land m n := Nat.landAux m m n
```

**The guard order is `n = 0` OUTERMOST**, the mirror of `log.rs`'s `b ≤ n`
ordering and for the identical reason: only the outermost cut collapses the
whole succ-step term with one rewrite, independent of the (possibly
symbolic) fuel predecessor. This makes `land m 0 = 0` an easy induction on
`m` where every step is `refl` with the induction hypothesis unused —
`log_zero_left`'s exact shape. `land 0 n = 0` is even cheaper: fuel is `m =
0`, so the outer `Nat.rec` is already exhausted and the theorem is `refl`
with no induction at all.

Detail moved to [`../notes/215-nat-bitwise-2.md`](../notes/215-nat-bitwise-2.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise-2 | `Nat.land`/`Nat.landAux` (structural fuel recursion, direct — not through `Nat.bitwise`) plus `land_zero_left`/`land_zero_right`/`land_one_one`/`land_three_five`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-land-*` facts; `Nat.bitwise`/`Nat.lor`/`Nat.ldiff`/`Nat.bits` scoped out |
