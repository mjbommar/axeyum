# 259 -- nat-bitwise-bit-swap (lane `nat-bitwise-bit-swap`)

<!-- plan-section: lane-status -->

Status: `bitwise_swap` LANDED and closed. `bitwise_bit'` NOT attempted --
sized only in this file's earlier plan section, per the brief's "landing
one of the two is a good outcome."

## Task
- `F:ml430-nat-bitwise-swap-7175e90e` (`Nat.bitwise_swap`) -- primary
  target. **DONE**, flipped to `proved`.
- `F:ml430-nat-bitwise-bit-4c4b28a8` (`Nat.bitwise_bit'`) -- secondary.
  **NOT attempted.** Still `open`.

## `bitwise_swap`: what was built and why

### Simpler than `bitwise_comm`, and why

`bitwise_swap` states (pointwise, no `funext`): `forall f m n, Eq (bitwise
(swap f) m n) (bitwise f n m)` where `swap f := fun a b => f b a`. Unlike
`bitwise_comm`, it needs **no hypothesis on `f` at all**: `swap f` applied
to any two `Bool`s beta-reduces DIRECTLY to `f` applied to them in the
other order, because the swap is baked into which function gets applied
rather than asserted about a fixed one. Every site `bitwise_comm` needed
`hf : forall a b, f a b = f b a` plus `congr_bool_to_nat` for (the two
boundary rows and the per-bit combine) becomes pure defeq here.

Confirmed by hand-substitution (not Python -- the recursion is small enough
to trace directly by expanding `bitwiseAux (swap f) fuel m n` and
`bitwiseAux f fuel n m` case-by-case) BEFORE writing any Rust: every row
matches by beta/iota alone except the both-nonzero recursive step, which
needs exactly the induction hypothesis. Even there, the per-bit "bit" term
matches the other side EXACTLY (same term, after the beta-swap), so only
the recursive sub-call needs a `d.congr` -- no `bit`-side congruence at
all, unlike `bitwise_comm`'s `bitwise_bit_comm`.

### The two lemmas landed (`nat_prelude/bitwise.rs`, uncontended)

Detail moved to [`../notes/259-nat-bitwise-bit-swap.md`](../notes/259-nat-bitwise-bit-swap.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-bitwise-bit-swap | Land `Nat.bitwise_swap` (`nat_prelude/bitwise.rs`): a fuel-induction cross lemma (`bitwise_aux_swap_of_fuel`) needing NO commutativity hypothesis, since `swap f` beta-reduces to `f` with arguments exchanged; close `F:ml430-nat-bitwise-swap-7175e90e`. Also fixed a pre-existing merge artifact in `nat_prelude_tests.rs` that had silenced `clog_computes_and_its_boundary_equations_apply` as dead code. `bitwise_bit'` remains open. |
