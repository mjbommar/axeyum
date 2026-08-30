# Lane: nat-testbit-xor — `Nat.testBit_xor`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.testBit_xor landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 3 pieces remain)`, nat-testbit-xor, 2026-08-29).**

## What landed

New file `crates/axeyum-lean-kernel/src/nat_prelude/testbit_bitwise.rs`:

```
Nat.testBit_xor : ∀ m n i,
  Eq (testBit (xor m n) i) (xor_bit (testBit m i) (testBit n i))
```

where `xor_bit(x, y) := bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` —
the same per-bit combine `bitwiseAux`'s own `succ_minor` row builds at bit
0 (`bitwise.rs`), generalized here to an arbitrary bit position.

This is piece (1) of the 4 pieces `docs/plan/status/260-nat-lt-xor-cases.md`
named as blocking `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`).
Admitted by the trusted kernel gate on the first attempt — no failed
`add_declaration` calls, no bisecting.

## Codomain check: local fact, not an `ml430` mirror

Mathlib's `testBit` returns `Bool`; this kernel's returns `Nat` in `{0,1}`
(`nat_prelude/binary.rs`'s module doc) — the same codomain mismatch that
made six sibling `testBit`-family mirrors unflippable (per the
`260-nat-lt-xor-cases.md` handoff and `F:nat-zero-of-testbit-eq-zero`'s own
note). No `ml430` fact for this exact statement was found in the ledger.
Landed as a new local fact, `F:nat-testbit-xor`
(`artifacts/facts/F-nat-testbit-xor.json`), `epistemic_status: proved`,
`axiom_footprint: []`, three independently-checked evidence rows (kernel
presence, concrete+symbolic compute, whole-prelude axiom-freedom).

## Keeping the two recursions in step

Detail moved to [`../notes/263-nat-testbit-xor.md`](../notes/263-nat-testbit-xor.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-testbit-xor | Landed `Nat.testBit_xor` (new `nat_prelude/testbit_bitwise.rs`), bridging `testBitAux`'s index recursion with `bitwiseAux`'s value recursion via an induction on the bit index generalized over both operands, reduced to two new per-step lemmas (`xor_low_bit`, `xor_div_two`) that reuse `xor_parity.rs`'s one-step-unfold technique and `bitwise.rs`'s fuel-irrelevance machinery; admitted by the trusted kernel gate on the first attempt, axiom-free; registered as a new local fact `F:nat-testbit-xor` (codomain mismatch with Mathlib's `Bool`-valued `testBit` rules out an `ml430` mirror flip); piece (1) of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`, which stays `open` — pieces 2-4 unchanged from `docs/plan/status/260-nat-lt-xor-cases.md` |
