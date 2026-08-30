# Lane: nat-msb-order -- `Nat.exists_most_significant_bit` / `Nat.lt_of_testBit`

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL (piece 3 landed as F:nat-lt-of-testbit; piece
2 open, precise diagnosis recorded)`, nat-msb-order, 2026-08-29).**

## What landed

1. `Nat.self_lt_two_pow : forall n, Lt n (pow 2 n)` and
   `Nat.self_lt_two_pow_add : forall a b, Lt a (pow 2 (add a b))`
   (`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`, new file) --
   general, self-contained arithmetic (no dependency on `size`/`testBit`
   machinery). `self_lt_two_pow_add` is the key tool: it lets a proof bound
   TWO independent values (`n`, `m`) by ONE common power of two (apply it at
   `a := n` and `a := m` with the other value folded into `b`) without any
   general `Le`-based `pow` monotonicity lemma -- this prelude has only the
   STRICT, same-base `pow_lt_pow_of_lt`.
2. **`Nat.lt_of_testBit`** (piece 3 of 4): admitted, axiom-free, on the
   FIRST real kernel-check attempt (only Rust-level `E0499`
   nested-mutable-borrow errors needed fixing first). Registered as
   `F:nat-lt-of-testbit` -- see that fact and the module doc in
   `bit_order.rs` for the full route (`N := add n (add m (succ i))`, split
   via the pre-existing `Nat.sumRange_split`, tails identified via
   `sumRange_congr`).

## Codomain verdict for `F:ml430-nat-lt-of-testbit-72f64ab8`

Detail moved to [`../notes/265-nat-msb-order.md`](../notes/265-nat-msb-order.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-order | Landed `Nat.self_lt_two_pow`/`Nat.self_lt_two_pow_add` (new general arithmetic toolkit, `nat_prelude/bit_order.rs`) and `Nat.lt_of_testBit` (piece 3 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`, registered as the new local fact `F:nat-lt-of-testbit` since Mathlib's `testBit` is `Bool`-valued and this kernel's is `Nat`-valued), admitted axiom-free on the first real kernel-check attempt via a `sumRange_split`-based decomposition around a common bound `N := add n (add m (succ i))`; piece 2 (`exists_most_significant_bit`) diagnosed but NOT landed -- its "zero above the top bit" half has a specified cheap route (reusing this lane's own bound-construction technique), its "highest bit really is set" half remains a full lane needing a new `size`-recursion lemma or an independent bottom-up construction |
