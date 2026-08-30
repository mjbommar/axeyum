# Lane: nat-lt-xor-cases — `Nat.lt_xor_cases`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.xor_comm landed; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, precise diagnosis recorded)`, nat-lt-xor-cases, 2026-08-29).**

## The exact Mathlib statement

Read directly from the pinned checkout
(`/data0/axeyum/lean-import-toolchain/mathlib4`, confirmed at commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, matching the fact's own
`prior_art.where`), `Mathlib/Data/Nat/Bitwise.lean:296`:

```lean
theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c
```

Matches `artifacts/facts/F-ml430-nat-lt-xor-cases-c43a1e85.json`'s
`formal.statement` verbatim (`∀ {a b c : ℕ}, a < b ^^^ c → a ^^^ c < b ∨ a
^^^ b < c`).

## Codomain check: does NOT block a flip

Six sibling `testBit`-family mirrors turned out unflippable because
Mathlib's `testBit` returns `Bool` against our `Nat`-valued `testBit`. This
statement mentions no `testBit` at all — every quantifier is `Nat`, every
operator (`<`, `^^^`, `∨`) already exists with a matching codomain in this
prelude, and `Nat.xor` is already the same `bitwise xor` shape Mathlib
uses. **An honest flip is possible once proved.** It is not proved here.

## What landed: `Nat.xor_comm`

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_order.rs`:

```
Nat.xor_comm : ∀ m n, Eq (xor m n) (xor n m)
```

Detail moved to [`../notes/260-nat-lt-xor-cases.md`](../notes/260-nat-lt-xor-cases.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lt-xor-cases | Read the pinned Mathlib v4.30 source for `Nat.lt_xor_cases` directly (no codomain block — fully `Nat`-valued); landed `Nat.xor_comm` (new `nat_prelude/xor_order.rs`, a corollary of `Nat.bitwise_comm` at `f := xor_fn`, one of the pieces Mathlib's own proof route composes) with a discriminating evaluation test; repaired an unrelated pre-existing merge-splice `#[test]`-attribute bug in `nat_prelude_tests.rs` that `cargo clippy -D warnings` exposed; `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — precise diagnosis of the 4 remaining substantial pieces (`testBit_xor`, an `exists_most_significant_bit` equivalent, `lt_of_testBit`, `xor_assoc`/`xor_xor_cancel`/`xor_ne_zero_iff`) recorded in `xor_order.rs`'s module doc and this file |
