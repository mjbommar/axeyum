# 262 -- nat-bitwise-bit-prime (lane `nat-bitwise-bit-prime`)

<!-- plan-section: lane-status -->

**Status: `DONE`.** `Nat.bitwise_bit'` (`F:ml430-nat-bitwise-bit-4c4b28a8`) is
landed, closing the last open member of the `Nat.bit`-decode `*_bit` family.
All four (`land_bit`, `lor_bit`, `ldiff_bit`, `bitwise_bit'`) are now `proved`.

## Task

- `F:ml430-nat-bitwise-bit-4c4b28a8` (`Nat.bitwise_bit'`) -- primary and only
  target, scoped by `docs/plan/status/259-nat-bitwise-bit-swap.md`. **DONE**,
  flipped to `proved`.

## What was built, in `nat_prelude/bitwise.rs` (uncontended at landing time)

The statement: `∀ f (a : Bool) (m : Nat) (b : Bool) (n : Nat), (m = 0 -> a =
true) -> (n = 0 -> b = true) -> bitwise f (bit a m) (bit b n) = bit (f a b)
(bitwise f m n)`.

**The fuel-swap machinery transports unchanged from `bit_decode.rs`'s
`land_bit`**, exactly as `docs/plan/status/259`'s sizing note predicted: an
artificially `succ`-shaped fuel (`base := mul 2 m`, `k1 := succ base`, `fuel
:= succ k1`), both `Le` bounds unconditional in `a`/`b`, then a `refl`-unfold
to the shared `guarded` step. `bitwise_aux_agree_of_fuel` (already declared
inside `declare_bitwise_comm`, general over ANY `f` -- no commutativity
needed) does BOTH fuel-swap steps directly, simpler than `land_bit`'s own
`land_aux_eq_land_of_le` two-step (no `symm` needed anywhere in the chain).

**Two things are new, both specific to a symbolic `f`, and both sized
correctly by `docs/plan/status/251`'s and `259`'s own diagnoses:**

Detail moved to [`../notes/262-nat-bitwise-bit-prime.md`](../notes/262-nat-bitwise-bit-prime.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-bitwise-bit-prime | Land `Nat.bitwise_bit'` (`nat_prelude/bitwise.rs`): the generic-`f` counterpart of `bit_decode.rs`'s `land_bit`/`lor_bit`/`ldiff_bit`, needing a new `Bool`-round-trip lemma (`cond_beq_one_eq_self`) for the per-bit combine and a new "generalize with equality" case-split (`cases_zero_succ_with_eq`) to discharge the two side hypotheses that close a leading-zero ambiguity the fixed-`f` specializations never have. Kernel accepted on the first attempt. Closes `F:ml430-nat-bitwise-bit-4c4b28a8`, proved axiom-free -- all four `Nat.bit`-decode `*_bit` facts are now closed. |
