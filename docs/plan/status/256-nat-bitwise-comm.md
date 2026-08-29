# 256 -- nat-bitwise-comm (lane `nat-bitwise-comm`)

Status: IN PROGRESS (WIP commit, code not yet written).

## Task
- `F:ml430-nat-bitwise-comm-1a273bae` (`Nat.bitwise_comm`) -- primary target.
- `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`) -- secondary, only if time remains.

## Findings so far

Python simulation (`/tmp/.../nat-bitwise-comm-nat-bitwise-comm.sim.py`, not
committed -- scratchpad) confirms the brief's prediction exactly:

- Unconditional `bitwiseAux f fuel m n = bitwiseAux f fuel n m` (fuel not
  necessarily sufficient) is FALSE for `f = or` and `f = xor` (both have
  `f false true = true`): `bitwiseAux(or, 0, 0, 1) = 1` but
  `bitwiseAux(or, 0, 1, 0) = 0`. It IS true for `f = and` (`f false true =
  false`, matching `land`'s absorbing-zero row).
- With `Le m fuel` AND `Le n fuel` (sufficient fuel for both operands), the
  statement holds for all three (0 counterexamples over 2000 random trials
  each, `fuel` up to `max(m,n)+5`).
- `bitwise f m n = bitwise f n m` (canonical fuel) holds for and/or/xor over
  the full `0..60` grid.

So `bitwise_aux_comm_of_fuel` needs the `lor` shape (`Le m fuel -> Le n fuel
-> ...`), exactly as flagged, plus a `∀ a b, f a b = f b a` hypothesis since
`f` is symbolic (lor/land don't need this because their `f` is fixed and
concrete).

## Plan

Mirror `lor`'s fuel-irrelevance + comm construction in `rec_agreement.rs`,
generalized over a symbolic `f`, landing in `bitwise.rs` (uncontended):

1. `bitwise_aux_zero_left_any_fuel : forall f fuel n, Eq (bitwiseAux f fuel 0 n)
   (bool_select_nat (f false true) n 0)` -- unconditional in `f`, structural,
   same proof shape as `land_aux_zero_left_any_fuel`.
2. `bitwise_aux_agree_of_fuel` (double-fuel induction, generalized over `f`) --
   same shape as `land_aux_agree_of_fuel`/`lor_aux_agree_of_fuel`.
3. `bitwise_aux_comm_of_fuel` (single fuel, `Le m fuel -> Le n fuel -> hf ->
   ...`) -- same shape as `lor_aux_comm_of_fuel`, with the per-bit swap
   argument threaded through `hf : forall a b, f a b = f b a` instead of a
   fixed lemma like `mul_comm`/`lor_bit_comm`.
4. `bitwise_comm` -- assembled via the shared fuel `m + n`, exactly as
   `land_comm`/`lor_comm`.

Needs `half_le_predecessor_of_succ` and `n_lt_mul_two` from
`rec_agreement.rs`, both fully generic already (no land/lor-specific
content) but currently private -- plan is a 2-line visibility-only change
(`fn` -> `pub(super) fn`) rather than duplicating ~40 lines of arithmetic.

Continuing now.
