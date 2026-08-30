# Notes: 263-nat-testbit-xor

Detail moved out of [`../status/263-nat-testbit-xor.md`](../status/263-nat-testbit-xor.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`testBitAux` recurses on the bit INDEX `i` (`testBit_succ`, `refl`:
`testBit n (succ i) ≡ testBit (n/2) i`); `xor` recurses on FUEL derived
from the VALUE (`bitwiseAux`, fuel = the first operand's magnitude). The
bridge is an induction on `i`, generalizing over BOTH `m` and `n` in the
motive — the same "generalize the OTHER variable" device
`testBit_le_one`/`sum_testBit_lt` use for one variable, widened to two
since `xor` genuinely mixes them (`d.induct` with a motive
`fun i => ∀ m n, Eq (testBit (xor m n) i) (xor_bit (testBit m i) (testBit
n i))`) — reduced at each level to two per-step lemmas that do NOT mention
`i` at all:

- **`xor_low_bit`** (private helper): `Eq (mod (xor m n) 2) (xor_bit (mod
  m 2) (mod n 2))`. Closes the induction's BASE case, since `testBit _ 0`
  is `refl`-defeq to `mod _ 2`. This generalizes `xor_parity.rs`'s
  `even_xor_hard_case` step (which stopped at `Iff Even`) to a plain `Eq`,
  and additionally covers the `m = 0`/`n = 0` boundary cases via
  `cases_mod_two` (`even_xor` handled those with a different "one side of
  an `Iff` is always true" device that has no `Eq`-shaped analogue).
- **`xor_div_two`** (private helper): `Eq (div (xor m n) 2) (xor (div m 2)
  (div n 2))`. Closes the STEP case, since `testBit _ (succ j)` is
  `refl`-defeq to `testBit (_/2) j`; `d.congr` along this equation
  transports the IH from `(m/2, n/2)` back to `(m, n)`. This is new
  content — nothing in the prelude related `xor`'s recursive tail to `xor`
  of the halved operands before this file. The both-nonzero case needs
  `Nat.bitwise_aux_agree_of_fuel` (fuel-irrelevance, `bitwise.rs`) to
  bridge the exposed fuel `pm` (one less than `m`) to the CANONICAL fuel
  `m/2` that `xor (m/2) (n/2)`'s own definition uses, via
  `half_le_predecessor_of_succ` (`rec_agreement.rs`) for the sufficiency
  bound `Le (m/2) pm`.

Both lemmas share the same "one step of `bitwiseAux`'s recursor" case
analysis (`m = 0`; `n = 0` with `m` exposed `succ`-shaped; both `succ`),
bundled in a private `XorStep` struct/`xor_step` function so the recursive
term, the per-bit combine, and its `< 2` bound are computed once and
reused by both — mirroring `xor_parity.rs::even_xor_hard_case`'s own
construction throughout.

Two small local helpers were duplicated rather than exposed from sibling
files mid-work by other lanes (`xor_parity.rs`'s private `xor_bit`;
`parity.rs`'s `mod_two_mul_add_of_lt` needed a DIV-sibling,
`div_two_mul_add_of_lt`, built by swapping `and_right` for `and_left` on
the identical `divMod`-uniqueness witness) — both are `pub(super)` in the
new file in case a later lane wants them.

## Evidence

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **145 passed, 0
  failed** (144 before this lane, +1 new evaluation test).
- New test
  `test_bit_xor_applies_at_a_concrete_discriminating_instance_and_symbolically`
  (`nat_prelude_tests.rs`): checks all THREE meaningfully differing bits of
  `xor 5 3 = 6` (`101 ^ 011 = 110`: bit 0 both-`1`→`0`, bit 1 `0`/`1`→`1`,
  bit 2 `1`/`0`→`1`) against independently hand-computed values, each with
  a negative control asserting the OTHER bit value does not also `def_eq`
  — one bit position alone could not discriminate a swapped combine — AND
  symbolically against a genuinely free `(m, n, i)` triple wrapped in a
  fresh `d.theorem(...)` (the same pattern `xor_comm_restated` uses, since
  raw test-created fvars fail `Kernel::infer` with `UnboundFVar`).
- `cargo fmt --all --check` clean (read-only; no destructive workspace
  format was run — files formatted individually with
  `rustfmt --edition 2024 <file>` per the multi-agent hygiene rule).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
- `python3 scripts/validate-facts.py` — 1938 facts, 0 errors.
- `the_build_is_deterministic` pin: `93 + 495` → `93 + 496` (one new
  theorem name added to `theorem_names`), taken from the panic's own
  mismatch after adding `p.test_bit_xor` to the list — the panic on
  `every_nat_declaration_is_checked_and_axiom_free` (which is
  environment-derived, not list-derived) caught the missing registration
  first, exactly as that assertion is designed to.

Workspace gate NOT run (coordinator re-verifies before merging, per the
lane brief). Not pushed.

## What `F:ml430-nat-lt-xor-cases-c43a1e85` still needs

Stays `open`. Piece (1) is done. Pieces 2-4, unchanged from
`docs/plan/status/260-nat-lt-xor-cases.md` (each independently substantial,
its own lane):

1. ~~`testBit_xor`~~ — **DONE, this lane.**
2. **`exists_most_significant_bit`-equivalent**: `∀ n, n ≠ 0 → ∃ i,
   testBit n i = 1 ∧ ∀ j, i < j → testBit n j = 0`. Needs induction
   connecting `sizeAux`'s recursion to `testBitAux`'s (natural witness
   `pred (size n)`, via `Nat.size`/`Nat.lt_pow_size`, `binary.rs`).
3. **`lt_of_testBit`-equivalent**: bit-`i` disagreement plus agreement
   above `i` forces the order. Needs relating "agreement above `i`" to a
   quotient equality (`n / 2^(i+1) = m / 2^(i+1)`) — the SAME
   `xor_div_two`-style "halved-operand" bridge this lane built could be a
   useful template (relating a value's shifted form to a claim about its
   halves), but the statement itself is genuinely new, not a corollary.
4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`**. No
   `_assoc`-shaped machinery exists in this prelude for ANY bitwise
   operator yet (only `_comm` forms do); `testBit_xor` (this lane) could
   plausibly be the route in for `xor_ne_zero_iff` specifically (a natural
   at bit `i` witnesses `Nat` nonzero, and `zero_of_testBit_eq_zero`
   already gives the contrapositive), but that composition was not
   attempted here.

`testBit_xor`'s statement itself (piece 1) is a load-bearing ingredient for
piece 3 in particular — Mathlib's own `lt_of_testBit` doesn't need it, but
any route through THIS prelude's low-level `mod`/`div` machinery for the
"agreement above `i`" step is likely to want `testBit_xor` or its
`xor_low_bit`/`xor_div_two` internals.

## Commits (this lane)

1. `wip(nat): testbit_bitwise.rs scaffold -- Nat.testBit_xor draft, NOT wired in`
   — the new file, landed early (before wiring/testing) per the ten-tool-call
   rule.
2. `wip(nat): wire testbit_bitwise into nat_prelude.rs -- compiles, untested`
   — `mod testbit_bitwise;`, the `test_bit_xor` NameId + registration,
   dispatch call.
3. (pending at write time) — the coverage-list fix
   (`theorem_names` + `the_build_is_deterministic` pin), the evaluation
   test, the `xor_bit` visibility widening (`fn` → `pub(super) fn<D:
   NatOps>`, needed so the test crate could build the expected RHS the same
   way production code does), and the new fact
   `artifacts/facts/F-nat-testbit-xor.json`.
