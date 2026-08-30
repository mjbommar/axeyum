# Lane: nat-bitwise — unblock `Nat.bit` and its boundary lemmas

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-bitwise, 2026-08-28).**

The frontier reported `Nat.bit`, `Nat.bitwise`, `Nat.bits`, `Nat.ldiff` as
BLOCKED — undeclared kernel definitions, so the `F:ml430-nat-bitwise-*` /
`F:ml430-nat-land-bit-*` / `F:ml430-nat-lor-bit-*` / `F:ml430-nat-ldiff-bit-*`
mirror facts could not even be *stated*. Per the brief, only `Nat.bit` was
attempted — it is the cheapest of the four and unblocks the most — and
landing it plus real boundary lemmas was the target for a complete success.

**`Nat.bit` landed, and it needed no fuel device at all.** Mathlib defines
`bit b n := cond b (2*n+1) (2*n)` — a plain case split on the `Bool`
argument, no recursive call anywhere. Unlike `Nat.log`/`Nat.sqrt`/`Nat.clog`
(all landed earlier the same day, all non-structural and requiring the fuel
device this prelude uses for `Nat.div`/`Nat.mod`), `Nat.bit` is declared as
an ordinary non-recursive lambda: `bit b n := add (mul 2 n) (cond b 1 0)`.

**The `add`-outermost form (rather than Mathlib's `cond`-outermost one) was
a deliberate choice, not an accident of translation.** Both normalize to the
same value at every literal `b` — `add x zero ≡ x` collapses the false
branch to `2n`, `add x (succ zero) ≡ succ (add x zero) ≡ succ x` collapses
the true branch to `succ (2n) = 2n+1` — but the `add`-outermost form buys
something Mathlib's shape does not: `bit true n` unfolds all the way to
`succ (mul 2 n)` by delta+iota alone, so a lemma about `succ` in general
(`zero_lt_succ`, `le_succ`) applies to it **directly by defeq, with no
case-split combinator**. `log.rs`'s `le_of_bool_select` had to build that
combinator by hand for the analogous situation in `Nat.log`; `bits.rs` never
needed to.

**Four theorems landed, all on the first `Kernel::add_declaration` attempt —
nothing was rejected:**
- `bit_false : ∀ n, bit false n = mul 2 n` — `Eq.refl`.
- `bit_true : ∀ n, bit true n = add (mul 2 n) 1` — `Eq.refl`.
- `bit_true_pos : ∀ n, 0 < bit true n` — `zero_lt_succ (mul 2 n)`, accepted
  by defeq against the unfolded statement.
- `bit_false_le_bit_true : ∀ n, bit false n <= bit true n` — `le_succ
  (mul 2 n)`, accepted by defeq the same way.

Detail moved to [`../notes/207-nat-bitwise.md`](../notes/207-nat-bitwise.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise | `Nat.bit` (non-recursive, no fuel needed) plus `bit_false`/`bit_true`/`bit_true_pos`/`bit_false_le_bit_true`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-bit-*` facts; `Nat.bitwise`/`Nat.bits`/`Nat.ldiff` scoped out |
