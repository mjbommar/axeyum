# Notes: 260-nat-lt-xor-cases

Detail moved out of [`../status/260-nat-lt-xor-cases.md`](../status/260-nat-lt-xor-cases.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

A direct corollary of the already-landed `Nat.bitwise_comm` (general in
`f`) at `f := xor_fn`, needing only a Boolean commutativity witness for
`xor_fn` built by the exact same nested-`Bool.rec` construction
`nat_prelude_tests.rs::bool_fn_comm` already builds and already tests at
`f := xor_fn` (`bitwise_comm_applies_at_a_concrete_discriminating_instance`)
— production code reusing a proven pattern, not a new technique. This is
genuine progress toward the target, not an unrelated bonus: Mathlib's own
`xor_trichotomy` proof (which `lt_xor_cases` is built on) calls
`Nat.xor_comm` twice, in its `hbc`/`hca` steps.

Evaluation test `xor_comm_applies_at_a_concrete_discriminating_instance_and_symbolically`
(`nat_prelude_tests.rs`): the same `(3, 5)` discriminating pair every
sibling `_comm` theorem uses, plus a symbolic build at a genuinely free
`(m, n)` pair, wrapped in a fresh `d.theorem(...)` call the same way
`bitwise_comm`'s own test does — a first attempt calling `Kernel::infer`
directly on raw test-created fvars failed with `UnboundFVar` (fvars need a
local-context registration that `pi_fv`/`lam_fv` inside `d.theorem`
supplies and a bare `f.k.fvar(fv)` does not).

`the_build_is_deterministic` pin: `93 + 489` -> `93 + 490` (one new
theorem), taken from the panic's own `left: 583` value.

## An unrelated merge-splice bug this lane's build exposed

`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` failed
on TWO pre-existing defects in `nat_prelude_tests.rs`, present in the
merge from `main` before this lane touched anything (visible as two
non-fatal warnings in the very first `cargo test` run of this session):
`clog_computes_and_its_boundary_equations_apply`'s doc comment + `#[test]`
attribute had been spliced ahead of
`land_bit_applies_at_a_concrete_discriminating_instance`'s own doc +
`#[test]` by an earlier merge — leaving `clog`'s test function with NO
`#[test]` attribute (silently never run as a test, hence `dead_code`) and
`land_bit`'s function with two stacked `#[test]` attributes (`duplicated
attribute`). Repaired by moving `clog`'s doc+attribute back to sit
directly above its own function; neither function's body was touched.
This is exactly the "additive merge conflict cuts mid-item" hazard
CLAUDE.md documents for `#[test] fn` bodies, from three sibling `nat_xor`
lanes landing on the same day.

## What `F:ml430-nat-lt-xor-cases-c43a1e85` still needs

Stays `open`. Full diagnosis is in `xor_order.rs`'s module doc (read that
file for the complete reasoning); summary here.

Mathlib's own proof route: `lt_xor_cases` <- `xor_trichotomy` (`a^^^b^^^c
≠ 0 → b^^^c<a ∨ c^^^a<b ∨ a^^^b<c`) <- `exists_most_significant_bit`
(highest set bit of a nonzero value) composed with `lt_of_testBit`
(agreement above a differing bit + differing at it ⟹ the order), plus
`xor_assoc`/`xor_xor_cancel_{left,right}`/`xor_ne_zero_iff` to route
`xor_trichotomy`'s hypothesis through `xor_assoc _ _ _ ▸ xor_ne_zero_iff`.

**This prelude has more of the needed machinery than either prior lane's
report credits** — `binary.rs`'s `size` addendum (`declare_size_all`,
dispatched separately from `declare_binary_all`) already has:

- `Nat.size`, `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))`.
- `Nat.sum_testBit_eq : ∀ n, sumRange (fun i => testBit n i * 2^i) (size
  n) = n` — a number IS the sum of its own bits.
- `Nat.zero_of_testBit_eq_zero : ∀ n, (∀ i, testBit n i = 0) → n = 0` —
  the contrapositive half of "a nonzero number has some set bit".

**Confirmed absent** (fresh `--release` `prelude_theorem_inventory
--include-constructed`, `distinct: theorems=1743`, `preludes=...,nat,...`,
so the tool covers this prelude): `Nat.lt_xor_cases`, `Nat.xor_assoc`,
any spelling of `testBit_xor`, any "most significant bit" construction,
any `lt_of_testBit` analogue. **Confirmed present**: `Nat.bitwise_comm`,
`Nat.size`, `Nat.lt_pow_size`, `Nat.zero_of_test_bit_eq_zero`,
`Nat.sum_test_bit_eq`, and now `Nat.xor_comm`.

Four pieces are still missing, each independently substantial (comparable
in scope to `binary.rs`'s `size` addendum or `rec_agreement.rs`'s
fuel-agreement lemmas on its own — i.e. its own lane, not a follow-on):

1. **`testBit_xor`-equivalent**: `testBit (xor m n) i` in terms of
   `testBit m i`/`testBit n i`. Needs a NEW agreement lemma between
   `testBitAux`'s index-recursion and `bitwiseAux`'s value-recursion at a
   symbolic bit position — different in kind from `rec_agreement.rs`'s
   existing agreements (which relate two VALUE-recursions at fixed fuel).
2. **`exists_most_significant_bit`-equivalent**: `∀ n, n ≠ 0 → ∃ i,
   testBit n i = 1 ∧ ∀ j, i < j → testBit n j = 0`. The natural witness is
   `pred (size n)`, but neither "`testBit n (pred (size n)) = 1` for
   `n ≠ 0`" nor "`testBit n j = 0` for `j ≥ size n`" is proved — each
   needs induction connecting `sizeAux`'s recursion to `testBitAux`'s,
   comparable in size to `size_aux_lt_pow` (~70 lines) per direction.
3. **`lt_of_testBit`-equivalent**: bit-`i` disagreement plus agreement
   above `i` forces the order. Needs relating "agreement above `i`" to a
   quotient equality (`n / 2^(i+1) = m / 2^(i+1)`), then a
   `sum_testBit_eq`-style decomposition bounding the tail below `2^i`.
   Genuinely new, not a corollary of anything above.
4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`**.
   `xor_assoc` specifically is what Mathlib's `bitwise_assoc_tac` exists
   for, and that tactic's own comment says associativity of a bitwise
   operator "essentially boils down to a huge case distinction" — nothing
   in this shape (`_assoc` for ANY bitwise operator) exists in this
   prelude yet, only `_comm` forms do.

Recommend a dedicated lane per missing piece, in the order above (each
later piece consumes the one before it), or a single lane scoped
explicitly to "build a highest-differing-bit `testBit` machinery for
`Nat`" rather than to `lt_xor_cases` specifically — the theorem itself is
the last, cheapest step once (1)-(4) exist.

## `scripts/gen-autogenesis-bitwise-family-projection.py`

Checked directly: names three unrelated `testBit` facts (per
`docs/plan/status/244-nat-testbit-bitwise.md`), not `lt-xor-cases`. Does
not pin this fact open independent of provability.

## Commits (this lane)

1. `feat(nat): Nat.xor_comm, new xor_order.rs (compiles; F:ml430-nat-lt-xor-cases stays open)`
   — the new file, `Nat.xor_comm`, prelude wiring. Landed early (before the
   test suite ran) per the ten-tool-call rule; compiled but not yet
   test-verified.
2. `test(nat): xor_comm evaluation test; fix a merge-splice bug found by clippy`
   — the evaluation test, the pin fix, and the unrelated
   pre-existing `#[test]`-splice repair in `nat_prelude_tests.rs`.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 140 passed, 0
failed (139 before this lane, +1 for `xor_comm`'s test). `cargo fmt --all
--check` clean. `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` clean (also fixed the pre-existing merge-splice defect this
gate exposed). `python3 scripts/validate-facts.py` — 1934 facts, 0 errors
(no fact files touched; `F:ml430-nat-lt-xor-cases-c43a1e85` correctly
remains `open`). Workspace gate NOT run (coordinator re-verifies before
merging, per the lane brief). Not pushed.
