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

New file: `crates/axeyum-lean-kernel/src/nat_prelude/xor.rs` (per the brief,
to avoid the `land.rs`/`lor.rs`/`ldiff.rs`/`rec_agreement.rs`/`binary.rs`
merge-conflict hot zone three sibling lanes were touching today). Wired into
`nat_prelude.rs`: `mod xor;`, `use xor::declare_xor_all;`, two new struct
fields (`xor`, `xor_three_five`), two name-assembly lines, and one
dispatcher call right after `declare_bitwise_all` (needs only `Nat.bitwise`,
nothing needs `Nat.xor`, so it goes immediately after).

**Evaluation test**, `xor_computes_and_is_bitwise_xor_fn`
(`nat_prelude_tests.rs`): a discriminating concrete table (`(3,5) -> 6`,
matching every sibling operator's own numeral at the same operand pair —
`land`=1, `lor`=7, `ldiff`=2/4, `xor`=6 — so a copy-paste from any neighbour
fails loudly), two negative controls (`xor 3 5` is neither `land`'s `1` nor
`lor`'s `7`), AND a separate symbolic check building `xor a b` against
`bitwise xor_fn a b` for a genuinely FREE fvar pair `a, b` (the CLAUDE.md
rule that a concrete instantiation can hide a defect a symbolic build
exposes — here the two constructions are the literal same term by
definition, so this is a low-risk but cheap and correct check to have).

`definition_names`/`theorem_names` (the environment-derived coverage
assertion `every_nat_declaration_is_checked_and_axiom_free` checks against)
both updated with the two new names.

**`the_build_is_deterministic` pin**: moved `88 + 459` -> `89 + 460`, taken
directly from the panic's own `left: 549` and cross-checked by counting `p.`
entries in each list independently (89, 460) — not hand-incremented.

**Verified**: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 131
passed, 0 failed (130 before this lane, +1 for the new test).
`cargo fmt --all --check` clean. `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `python3 scripts/validate-facts.py` —
1928 facts, 0 errors (no fact files were touched; both assigned facts
remain `open`, correctly).

## Why neither fact closes

**`F:ml430-nat-even-xor-78a39432`** (`Even (m ^^^ n) ↔ (Even m ↔ Even n)`):
our `Even`/`Odd` (`nat_prelude/parity.rs`, `∃ k, n = k+k` / `∃ k, n =
succ(k+k)`) is the SAME shape as Mathlib's generic `Even` (`∃ r, a = r+r`),
so an honest flip is possible IN PRINCIPLE once proved. But proving it needs
a bridge this prelude does not have: relating `Even`/`Odd` to the low bit of
a `bitwise`-family value. That bit is only exposed one `bitwiseAux`
fuel-step down (the `succ_minor` row's `combined_nat` term in `bitwise.rs`),
conditioned on both operands being nonzero — the `m = 0`/`n = 0` cases
return an *operand itself*, not a per-bit combine, so the general statement
needs its own case split before the per-bit argument even applies, and
nothing in this prelude currently connects `Nat.mod _ 2` to `Even`/`Odd` at
all (`parity.rs`'s own module doc notes it never needed that connection).
That is new machinery, not a corollary of defining `xor`.

**`F:ml430-nat-lt-xor-cases-c43a1e85`** (`a < b^^^c → a^^^c < b ∨ a^^^b <
c`): a highest-differing-bit argument (Mathlib's own proof inducts on
`testBit` disagreement). No existing lemma in this prelude gives that
argument a foothold, and it is unrelated in size to defining `xor` itself —
sizing it honestly puts it well outside a bitwise "add one operator" lane.

Both stay `open`; per the brief, "landing `Nat.xor` with an evaluation test
and neither fact closed is a good outcome" — that is where this lane lands.
Not checked against `scripts/gen-autogenesis-bitwise-family-projection.py`
for these two specifically: the script names three unrelated `testBit`
facts (per `docs/plan/status/244-nat-testbit-bitwise.md`), not these two, so
it does not pin them open independent of provability.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-xor-parity | Landed `Nat.xor := Nat.bitwise xor_fn` (new `nat_prelude/xor.rs`, reusing `bitwise.rs`'s existing `xor_fn`/`bitwise_xor_three_five` machinery — the same shape Mathlib v4.30 uses) with a discriminating evaluation test (concrete + free-variable); left `F:ml430-nat-even-xor-78a39432`/`F:ml430-nat-lt-xor-cases-c43a1e85` open, reasons recorded (both need machinery — a parity/low-bit bridge, a highest-differing-bit induction — well beyond defining `xor`) |
