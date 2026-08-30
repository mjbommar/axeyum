# Notes: 268-nat-xor-cancel

Detail moved out of [`../status/268-nat-xor-cancel.md`](../status/268-nat-xor-cancel.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Needed because the natural per-bit cancel identity `xor_bit x (xor_bit x y)
= y` is FALSE for a general `y : Nat` — confirmed by a Python truth-table
simulation before any Rust was written: `digitize(beq(y,1))` collapses any
`y >= 2` to `0` or `1` (`xor_bit(3, xor_bit(3, 5)) = 0 != 5`). `xor_assoc`'s
identity never needed this restriction because it stays at the
`digitize`/`Bool` level throughout; `xor_xor_cancel_left`'s conclusion is a
bare `y`, forcing a match back to the raw operand.

Route:

1. `Le y 1` lifts to `Lt y 2` via `Nat.le_succ_succ(y, 1, h_le) : Le (succ
   y) (succ 1)` — `succ (num 1)` is `refl`-defeq to `num 2` (both reduce to
   the identical unary term `succ (succ zero)`), so no separate lemma is
   needed for the bound itself.
2. `Nat.lt_two_cases(y, ·) : Or (Eq y 0) (Eq y 1)` splits the two cases.
3. The kernel's own (non-dependent) `Or.elim : (a b c : Prop) -> Or a b ->
   (a -> c) -> (b -> c) -> c` (`p.logic.or_elim`, `prelude.rs`) eliminates
   directly — **no new combinator was needed**; the brief's suggested
   "`Or`-elimination combinator" already exists as this kernel primitive,
   used the same way `order_more.rs`'s totality proofs and the
   `zero_or_succ_applies_at_a_compound_term_and_is_consumed_by_or_elim` test
   (named in the brief) use it.
4. Each branch (`h : Eq y 0` / `h : Eq y 1`) closes by `d.congr` along `h`
   to substitute the literal into `digitize(beq y 1)`, a `d.refl` at the
   computed literal (`digitize(beq 0 1)` computes to `0`; `digitize(beq 1
   1)` computes to `1` — the same "build refl of one side, let defeq do the
   rest" device `beq_digitize_one` uses), and `d.symm`/`d.trans` to route
   back through `h` to the bare `y`.

## Per-bit cancel lemma and the theorem-level wiring

`xor_bit_cancel_left(d, p, x, y, h_le_y) : Eq (xor_bit x (xor_bit x y)) y`
lifts a new `Bool`-level self-cancel lemma, `bool_xor_self_cancel_left :
Eq (xor_fn a (xor_fn a b)) b`, through the same digitize/round-trip
machinery `xor_bit_assoc` uses, landing on `y` itself via
`round_trip_le_one`. `bool_xor_self_cancel_left` is a 2-level `Bool.rec`
split: `a = false` closes by `refl` for ANY `b` (`xor_fn false w` reduces to
`w`, applied twice); `a = true` needs one more split on `b`, and BOTH leaves
close by `refl` directly — no third level, unlike `xor_assoc`'s
`bool_xor_assoc`.

`declare_xor_xor_cancel_left` applies `Nat.testBit_xor` (once, at `(a, xor a
b, i)` then again at `(a, b, i)` to substitute the inner value), then
`xor_bit_cancel_left` at `(testBit a i, testBit b i)` with `Nat.testBit_le_one`
supplying the `Le (testBit b i) 1` hypothesis, then closes with
`Nat.eq_of_testBit_eq`. `declare_xor_xor_cancel_right` transports from
`_left` via `Nat.xor_comm` twice (no new per-bit argument): `xor (xor a b) b
= xor (xor b a) b` (congr on `xor_comm a b`) `= xor b (xor b a)` (`xor_comm
(xor b a) b`) `= a` (`xor_xor_cancel_left b a`).

## A genuine bug, found via a bisecting probe (not by reading a poisoned suite)

Wiring `declare_xor_xor_cancel_left` into the live prelude poisoned all 152
`nat_prelude::` tests with one opaque `TypeMismatch`. Per the standing rule,
rather than reading it, the two new `declare_*` calls were temporarily
commented out of `declare_xor_algebra_all` and a throwaway `#[cfg(test)] mod
debug_probe` called each new helper directly against a (now-healthy) prelude:
`round_trip_le_one` and `xor_bit_cancel_left` both inferred correctly in
isolation (at both concrete `y := 0/1` and a genuinely free `x, y`), and so
did `bool_xor_self_cancel_left`. Calling `declare_xor_xor_cancel_left`
directly (bypassing the dispatcher) reproduced the `TypeMismatch` in one
step, with far more legible `expected`/`got` types than the full-suite
failure.

The defect: in the per-bit `bits_hyp` construction, the chain's second step
mislabeled its target. `xor_bit(tb_a, tb_b)` (the VALUE `testBit(xor a b,
i)` equals, via `test_bit_xor`'s inner lemma) was substituted directly as
the chain's next node, instead of being substituted INTO the outer
`xor_bit(tb_a, _)` combine first — i.e., confusing `xor_bit(tb_a, tb_b)`
(the substituted inner operand) with `xor_bit(tb_a, xor_bit(tb_a, tb_b))`
(the cascaded expression `xor_bit_cancel_left`'s own LHS shape actually
needs). Fixed by introducing an explicit `cascaded` intermediate
(`xor_bit(tb_a, xab_bit)`) and chaining through it. Two probe-and-rebuild
cycles found and fixed this; the debug_probe module was removed before the
final commit, per the standing rule.

## `Nat.xor_ne_zero_iff` — did NOT need the cancel lemmas; not attempted

The forward direction (`xor a b = 0 -> a = b`) does not need
`xor_xor_cancel_left`/`_right` at all — it is a direct corollary of
`Nat.eq_of_testBit_eq` plus `Nat.testBit_xor`: per bit, `testBit (xor a b) i
= 0` (via `test_bit_of_zero`) gives `xor_bit (testBit a i) (testBit b i) =
0` (via `test_bit_xor`), and the remaining step is a small `Bool`-level fact
(`xor_bit x y = 0 -> x = y` for `x, y <= 1`, via the SAME `{0,1}`
case-split shape `round_trip_le_one` and `xor_bit_cancel_left` already use —
reuse the round-trip machinery rather than re-deriving it). The reverse
direction (`a = b -> xor a b = 0`, via `xor a a = 0`, likely a short
`eq_of_testBit_eq` + `xor_bit`-self-cancellation-to-zero argument) and the
`Iff` packaging (`p.logic.iff`, `Iff.intro`) were not started. Neither
direction, nor the `Iff` wiring, was attempted this lane — time-boxed out
after landing both cancel lemmas plus their evidence and facts.

## What `Nat.lt_xor_cases` still needs

All four sub-targets Mathlib's `xor_trichotomy` proof composes
(`xor_assoc`, `xor_xor_cancel_left`, `xor_xor_cancel_right`,
`xor_ne_zero_iff`) are now landed except `xor_ne_zero_iff` itself — the last
gap in piece 4 of the 4 pieces `docs/plan/status/260-nat-lt-xor-cases.md`
named as blocking `F:ml430-nat-lt-xor-cases-c43a1e85`. Once
`xor_ne_zero_iff` lands, re-check `docs/plan/status/260-…` for whatever
`Nat.lt_xor_cases` needs beyond the four sub-targets themselves (the
highest-differing-bit argument `Nat.lt_of_testBit`/`exists_most_significant_bit`
already supply, per `docs/plan/status/263-nat-testbit-xor.md`'s own note that
`lt_xor_cases` mentions an UNBOUNDED part of the value and needs those, not
just the bounded per-bit identities this lane and its predecessor built).

## Commits (this lane)

1. `wip(nat): Nat.xor_xor_cancel_left/_right -- compiles, untested` — the
   round-trip lemma, the `Bool` self-cancel lemma, the per-bit cancel lemma,
   both `declare_xor_xor_cancel_left`/`_right`, wired into
   `declare_xor_algebra_all`, and the two new NameId fields in
   `nat_prelude.rs` — landed within the first ten tool calls, before
   compiling was confirmed against the trusted kernel gate.
2. (this commit) — the coverage-list fix (`theorem_names` +
   `the_build_is_deterministic` pin, `93 + 505` -> `93 + 507`), the
   bisected-and-fixed per-bit chain in `declare_xor_xor_cancel_left`, the
   concrete+symbolic evaluation test, the stale module-doc header fix in
   `xor_algebra.rs`, and the two new facts
   (`artifacts/facts/F-nat-xor-xor-cancel-left.json`,
   `artifacts/facts/F-nat-xor-xor-cancel-right.json`).

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **153 passed, 0
failed** (152 before this lane, +1: the new
`xor_xor_cancel_applies_at_a_concrete_discriminating_instance_and_symbolically`
test, confirmed running by name, `1 passed`, not `0 filtered out`).
`cargo fmt --all --check` clean. `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `python3
scripts/check-test-attribute-integrity.py` — 0 findings across 1,513 files.
`python3 scripts/validate-facts.py` — 1,945 facts, 0 errors. Both new facts'
`checker_command` lines re-run directly and confirmed passing (not merely
present in the JSON): the `nat_theorem_inventory` presence check for both
names, and `nat_axiom_inventory --require-axiom-free nat` reporting
`nat: axiom=0 opaque=0 quotient=0 total_trusted=0`. Workspace gate NOT run
(coordinator re-verifies before merging, per the lane brief). Not pushed.
