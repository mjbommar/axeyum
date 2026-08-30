# Lane: nat-xor-parity — `Nat.xor`, `Nat.even_xor`, `Nat.lt_xor_cases`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.xor landed; both assigned facts stay open,
reasons recorded)`, nat-xor-parity, 2026-08-29).**

## Step 0: does `Nat.xor` exist?

No — confirmed by grep (`bitwise.rs`'s own module doc says so explicitly:
"no prelude XOR sibling exists") and by the absence of any `mod xor;` under
`nat_prelude/`. No theorem-inventory tool was needed since the negative was
already explicit in source comments, not just an absent grep hit.

## What landed: `Nat.xor := Nat.bitwise xor_fn`

The "alternative worth checking first" the brief named was the right call.
`bitwise.rs` already carries the general `Nat.bitwise f m n` combinator
(landed by an earlier lane, `declare_bitwise_all`), already builds
`xor_fn` (`Bool.xor`, `pub(super)`) purely to instantiate `f` for its own
`bitwise_xor_three_five` sanity check, and that check already proves
`Eq (bitwise xor_fn 3 5) 6`. So `Nat.xor` did not need a fourth hand-rolled
`bitwiseAux`-shaped fuel recursion — it is a direct partial application:

```
Nat.xor := Nat.bitwise xor_fn      -- Nat -> Nat -> Nat
```

This is the SAME shape Mathlib v4.30 uses (`Mathlib.Data.Nat.Bitwise`:
`Nat.xor := bitwise xor`), not merely something pointwise-equal to it. The
absorbing-zero question the brief flagged (does the fuel operand carry the
operator's absorbing zero?) turned out to be moot for this definition: `xor`
inherits `bitwise`'s own general, `f`-independent boundary theorems
(`bitwise_zero_left`/`bitwise_zero_right`) rather than needing new
hand-written base-case rows. For the record (checked anyway, since the rule
is worth confirming even when not load-bearing): XOR is `lor`-shaped
(`0 xor n = n`), and `bitwise_aux`'s general fuel-exhaustion row
(`if f false true then n else 0`) reproduces exactly that at `f = xor_fn` by
δβι alone (`xor false true` reduces to `true`, so the row returns `n`) —
consistent with `bitwise.rs`'s own derivation for `lor`.

Detail moved to [`../notes/253-nat-xor-parity.md`](../notes/253-nat-xor-parity.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-xor-parity | Landed `Nat.xor := Nat.bitwise xor_fn` (new `nat_prelude/xor.rs`, reusing `bitwise.rs`'s existing `xor_fn`/`bitwise_xor_three_five` machinery — the same shape Mathlib v4.30 uses) with a discriminating evaluation test (concrete + free-variable); left `F:ml430-nat-even-xor-78a39432`/`F:ml430-nat-lt-xor-cases-c43a1e85` open, reasons recorded (both need machinery — a parity/low-bit bridge, a highest-differing-bit induction — well beyond defining `xor`) |
