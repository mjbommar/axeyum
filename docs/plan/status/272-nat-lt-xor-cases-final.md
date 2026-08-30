# Lane: nat-lt-xor-cases-final — `Nat.lt_xor_cases`, the composition step

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (F:ml430-nat-lt-xor-cases-c43a1e85 CLOSED -- Nat.xor_trichotomy and Nat.lt_xor_cases both admitted axiom-free on the first real kernel-check attempt)`, nat-lt-xor-cases-final, 2026-08-29).**

## What landed

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_trichotomy.rs`:

```
Nat.xor_trichotomy : ∀ a b c, Not (Eq (xor (xor a b) c) 0) →
  Or (Lt (xor b c) a) (Or (Lt (xor c a) b) (Lt (xor a b) c))
Nat.lt_xor_cases : ∀ a b c, Lt a (xor b c) →
  Or (Lt (xor a c) b) (Lt (xor a b) c)
```

Both admitted, axiom-free, on the FIRST real kernel-check attempt — no
`TypeMismatch` from the kernel at any point (only one Rust-level `E0499`
nested-mutable-borrow error needed fixing before `cargo check` passed, and
two more before the evaluation test compiled). This closes
`F:ml430-nat-lt-xor-cases-c43a1e85`, the last row `docs/plan/status/
260-nat-lt-xor-cases.md` identified as reachable, now that all four
blocking pieces landed earlier the same day:

1. `Nat.testBit_xor` (`F:nat-testbit-xor`, `testbit_bitwise.rs`)
2. `Nat.exists_most_significant_bit` (`F:nat-exists-most-significant-bit`,
   `bit_order.rs`, via `Nat.msb_exists_of_le_fuel`)
3. `Nat.lt_of_testBit` (`F:nat-lt-of-testbit`, `bit_order.rs`)
4. `Nat.xor_assoc`/`Nat.xor_xor_cancel_left`/`_right`/`Nat.xor_ne_zero_iff`
   (`F:nat-xor-assoc`, `F:nat-xor-xor-cancel-left`/`_right`,
   `F:nat-xor-ne-zero-iff`, `xor_algebra.rs`)

## Codomain check: confirmed, an honest flip

Detail moved to [`../notes/272-nat-lt-xor-cases-final.md`](../notes/272-nat-lt-xor-cases-final.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lt-xor-cases-final | Closed `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`) by composing the four pieces five prior lanes landed the same day (`testBit_xor`, `exists_most_significant_bit`, `lt_of_testBit`, `xor_assoc`/`xor_xor_cancel_left`/`_right`/`xor_ne_zero_iff`) via an auxiliary `Nat.xor_trichotomy` theorem following Mathlib's own proof route (read directly from the pinned v4.30 source, `Mathlib/Data/Nat/Bitwise.lean:266-297`); both admitted axiom-free on the first real kernel-check attempt (new file `nat_prelude/xor_trichotomy.rs`); the fact is fully `Nat`-valued so the flip is honest, unlike six sibling `testBit`-family mirrors this session found unflippable; `xor_xor_cancel_right` turned out unnecessary for the rotation identities, contra Mathlib's own tactic proof which uses it once |
