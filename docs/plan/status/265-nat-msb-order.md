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

**Stays `open`, confirmed before any proof work started.** `binary.rs`
confirms this kernel's `Nat.testBit : Nat -> Nat -> Nat` returns a value in
`{0, 1}` (`test_bit_of_zero : Eq (testBit 0 i) zero`, etc.), while Mathlib
v4.30's `Nat.testBit` returns `Bool`. A Nat-valued proof cannot honestly
flip that Bool-typed mirror -- matches the pattern of the six other
`testBit`-family mirrors this session found unflippable for the same
reason. `Nat.lt_of_testBit` landed as the new local fact `F:nat-lt-of-testbit`
instead, per the `F:nat-testbit-xor` precedent.

## Does `Nat.size` shortcut `exists_most_significant_bit`? (piece 2 -- NOT landed)

**Partially, and not for the hard half.** `binary.rs`'s existing `size`
addendum (`Nat.size`, `Nat.lt_pow_size : Lt n (pow 2 (size n))`,
`Nat.sum_test_bit_eq`, `Nat.zero_of_test_bit_eq_zero`) supplies real
machinery, but the statement splits into two halves of very different
difficulty, and `size` only helps the easier one:

- **"testBit n j = 0 for j >= size n" (upper tail is zero): tractable, NOT
  built.** This lane found a clean, self-contained ROUTE for it that does
  NOT need `size` at all -- reuse this lane's own `self_lt_two_pow_add`-style
  "pick a big enough `N`, decompose via `sumRange_split`" technique
  directly: given `n < pow 2 j` (from `Lt (size n) j` via a `pow`
  monotonicity argument, OR skip `size` ENTIRELY and just take `j` as the
  hypothesis directly: `n < pow 2 j -> testBit n j = 0`), `sum_test_bit_lt`
  at `k := succ j` and `k := j` both collapse `n`'s sum to `n` (via
  `mod_eq_self_of_lt`, since `n < pow 2 j <= pow 2 (succ j)` -- the second
  inequality via `pow_lt_pow_succ` then `n`'s own bound, or via THIS lane's
  `self_lt_two_pow_add` machinery run in reverse), and `sum_range_succ`
  forces the peeled term `testBit n j * pow 2 j` to be `0`, hence (since
  `pow 2 j != 0`) `testBit n j = 0`. Comparable in size to
  `value_eq_sum_range` in `bit_order.rs` (~15 lines) plus a short
  cancellation argument (~20 lines) -- a half-day item, not built here for
  time reasons.
- **"testBit n (pred (size n)) = 1 for n != 0" (the highest bit really is
  set): the genuinely hard half, NOT tractable from what exists today.**
  This needs a LOWER bound on `n` relative to `size n` (`2^(size n - 1) <=
  n`), which is NOT the same fact as `lt_pow_size`'s upper bound and is not
  a corollary of it -- `size`'s definition (`sizeAux n n`, a
  self-referential fuel choice) has no existing recursive-unfolding lemma
  relating `size n` to `size (n/2)` (the shape `size_aux_lt_pow` avoided
  needing, by generalizing over ANY sufficient fuel rather than the
  canonical one). Building this needs either (a) a NEW `size`-recursion
  lemma of that shape, or (b) an independent bottom-up construction (the
  `msbAux`-fuel induction sketched in `docs/plan/status/260-nat-lt-xor-cases.md`
  piece 2, which mirrors `declare_size_aux_lt_pow`'s own proof shape and
  size, ~150 lines). Neither was attempted here.

So: **piece 2 is NOT closed.** The "zero above" half is now a cheap
follow-on (this lane found and specified the route); the "highest bit is
set" half is still its own substantial lane, unchanged in size from the
`260` assessment.

## What `Nat.lt_xor_cases` (`F:ml430-nat-lt-xor-cases-c43a1e85`) still needs

Stays `open`. Of the four pieces `docs/plan/status/260-nat-lt-xor-cases.md`
named:

1. ~~`testBit_xor`~~ -- **DONE** (`nat-testbit-xor` lane, `F:nat-testbit-xor`).
2. **`exists_most_significant_bit`** -- **NOT DONE.** See above: the
   "zero above" half has a specified cheap route; the "highest bit set"
   half is still a full lane.
3. ~~`lt_of_testBit`~~ -- **DONE, this lane** (`F:nat-lt-of-testbit`).
4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`** --
   status not re-verified by this lane (briefed as a sibling lane's
   in-flight work at the start of this session; check `xor_algebra.rs`
   and `git log` before assuming it landed or is still open).

Once pieces 2 and 4 land, assembling `lt_xor_cases` itself from
`xor_trichotomy`'s route (`exists_most_significant_bit` composed with
`lt_of_testBit`, `xor_assoc`/`xor_xor_cancel_*`/`xor_ne_zero_iff` to route
the hypothesis) is comparatively small -- the expensive pieces are the
ones enumerated above, not the final composition.

## Commits (this lane)

1. `wip(nat): bit_order.rs scaffold -- Nat.self_lt_two_pow/self_lt_two_pow_add/lt_of_testBit, NOT yet proved`
<!-- was-absent: Nat.self_lt_two_pow -->
   -- new file, dispatcher wiring, three `NameId` fields, no-op body.
   Landed within the first ten tool calls per the standing rule.
2. `feat(nat): Nat.self_lt_two_pow, Nat.self_lt_two_pow_add -- admitted, axiom-free`
   -- both general lemmas, proved and tested; `theorem_names` +
   `the_build_is_deterministic` pin (93+498 -> 93+500).
3. `feat(nat): Nat.lt_of_testBit -- admitted, axiom-free; F:nat-lt-of-testbit`
   -- piece 3, the evaluation test, the pin (93+500 -> 93+501), and the new
   fact.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- **148 passed, 0
failed** (146 before this lane, +2 new evaluation tests:
`self_lt_two_pow_and_add_apply_at_concrete_and_symbolic_instances`,
`lt_of_test_bit_applies_at_a_genuinely_symbolic_hypothesis_set`; both
confirmed to run BY NAME, `1 passed` each, not `0 filtered out`).
`python3 scripts/check-test-attribute-integrity.py` -- 0 findings.
`cargo fmt --all --check` clean (files formatted individually with
`rustfmt --edition 2024 <file>`). `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `python3 scripts/validate-facts.py`
-- 1940 facts, 0 errors (new fact `F:nat-lt-of-testbit` added;
`F:ml430-nat-lt-xor-cases-c43a1e85` and `F:ml430-nat-lt-of-testbit-72f64ab8`
correctly remain `open`). Workspace gate NOT run (coordinator re-verifies
before merging, per the lane brief). Not pushed.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-order | Landed `Nat.self_lt_two_pow`/`Nat.self_lt_two_pow_add` (new general arithmetic toolkit, `nat_prelude/bit_order.rs`) and `Nat.lt_of_testBit` (piece 3 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`, registered as the new local fact `F:nat-lt-of-testbit` since Mathlib's `testBit` is `Bool`-valued and this kernel's is `Nat`-valued), admitted axiom-free on the first real kernel-check attempt via a `sumRange_split`-based decomposition around a common bound `N := add n (add m (succ i))`; piece 2 (`exists_most_significant_bit`) diagnosed but NOT landed -- its "zero above the top bit" half has a specified cheap route (reusing this lane's own bound-construction technique), its "highest bit really is set" half remains a full lane needing a new `size`-recursion lemma or an independent bottom-up construction |
