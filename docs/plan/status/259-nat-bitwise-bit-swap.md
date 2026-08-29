# 259 -- nat-bitwise-bit-swap (lane `nat-bitwise-bit-swap`)

Status: IN PROGRESS (plan committed early per lane protocol; code not yet
written).

## Task
- `F:ml430-nat-bitwise-bit-4c4b28a8` (`Nat.bitwise_bit'`)
- `F:ml430-nat-bitwise-swap-7175e90e` (`Nat.bitwise_swap`)

## Plan (derived by hand-simulating `bitwiseAux` before writing Rust)

`bitwise_swap` states (pointwise, no `funext`): `forall f m n, Eq (bitwise
(swap f) m n) (bitwise f n m)` where `swap f := fun a b => f b a`.

Key finding: unlike `bitwise_comm` (which needed an explicit `hf`
commutativity hypothesis and a propositional `Bool` congruence at every
swap site), `bitwise_swap` needs NO hypothesis on `f` at all, because
`swap_f` applied to any two arguments beta-reduces DIRECTLY to `f` applied
to the swapped arguments -- every site `bitwise_comm` needed
`congr_bool_to_nat`/`hf` for becomes a `d.refl`/pure-defeq step here, since
swapping happens by unfolding a literal lambda, not by invoking a
propositional equality. Hand-derivation (case-by-case comparison of
`bitwiseAux(swap f, fuel, m, n)` against `bitwiseAux(f, fuel, n, m)`)
confirms: fuel=0 boundary and the two succ-fuel zero-guard boundaries all
resolve by pure iota/beta once the relevant operand is exposed as
`0`/`succ _`; only the both-nonzero recursive step needs a genuine
induction hypothesis (fuel-generalized, same skeleton as
`bitwise_aux_comm_of_fuel`), and even there the per-bit "bit" term matches
the other side EXACTLY (same `ExprId`-equal term after the beta-swap), so
only the recursive sub-call needs `d.congr` over the IH -- no `bit_comm`
lemma needed.

Planned lemmas (`bitwise.rs`, mirroring `bitwise_aux_{zero_left_any_fuel,
agree_of_fuel, comm_of_fuel}`'s existing skeleton exactly, minus the `hf`
plumbing):
1. `swap_fn` helper: `fun a b => f_expr b a`.
2. `bitwise_aux_swap_of_fuel : forall f fuel m n, Le m fuel -> Le n fuel ->
   Eq (bitwiseAux (swap f) fuel m n) (bitwiseAux f fuel n m)` -- fuel
   induction via `agree_by_fuel_induction`, `cases_zero_succ` on m then n
   inside the succ branch, same shape as `bitwise_aux_comm_of_fuel`.
3. `bitwise_swap` -- assembled through shared fuel `m + n`, exactly as
   `bitwise_comm`'s final assembly (`bitwise_aux_agree_of_fuel` twice +
   `bitwise_aux_swap_of_fuel` once).

`bitwise_bit'` (side hypotheses `m = 0 -> a = true`, `n = 0 -> b = true`)
is the secondary target if time remains after `bitwise_swap`; not yet
scoped in detail.

## Commits (this lane, `nat-bitwise-bit-swap`)
1. (this commit) -- plan only, no code, per the "first commit within ten
   tool calls" protocol.
