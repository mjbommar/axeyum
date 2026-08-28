# Lane: nat-bitwise — unblock `Nat.bit` and its boundary lemmas

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-bitwise, 2026-08-28).**

The frontier reported `Nat.bit`, `Nat.bitwise`, `Nat.bits`, `Nat.ldiff` as
BLOCKED — undeclared kernel definitions, so the `F:ml430-nat-bitwise-*` /
`F:ml430-nat-land-bit-*` / `F:ml430-nat-lor-bit-*` / `F:ml430-nat-ldiff-bit-*`
mirror facts could not even be *stated*. Per the brief, only `Nat.bit` was
attempted — it is the cheapest of the four and unblocks the most — and
landing it plus real boundary lemmas was the target for a complete success.

**`Nat.bit` landed, and it needed no fuel device at all.** Mathlib defines
`bit b n := cond b (2*n+1) (2*n)` — a plain case split on the `Bool`
argument, no recursive call anywhere. Unlike `Nat.log`/`Nat.sqrt`/`Nat.clog`
(all landed earlier the same day, all non-structural and requiring the fuel
device this prelude uses for `Nat.div`/`Nat.mod`), `Nat.bit` is declared as
an ordinary non-recursive lambda: `bit b n := add (mul 2 n) (cond b 1 0)`.

**The `add`-outermost form (rather than Mathlib's `cond`-outermost one) was
a deliberate choice, not an accident of translation.** Both normalize to the
same value at every literal `b` — `add x zero ≡ x` collapses the false
branch to `2n`, `add x (succ zero) ≡ succ (add x zero) ≡ succ x` collapses
the true branch to `succ (2n) = 2n+1` — but the `add`-outermost form buys
something Mathlib's shape does not: `bit true n` unfolds all the way to
`succ (mul 2 n)` by delta+iota alone, so a lemma about `succ` in general
(`zero_lt_succ`, `le_succ`) applies to it **directly by defeq, with no
case-split combinator**. `log.rs`'s `le_of_bool_select` had to build that
combinator by hand for the analogous situation in `Nat.log`; `bits.rs` never
needed to.

**Four theorems landed, all on the first `Kernel::add_declaration` attempt —
nothing was rejected:**
- `bit_false : ∀ n, bit false n = mul 2 n` — `Eq.refl`.
- `bit_true : ∀ n, bit true n = add (mul 2 n) 1` — `Eq.refl`.
- `bit_true_pos : ∀ n, 0 < bit true n` — `zero_lt_succ (mul 2 n)`, accepted
  by defeq against the unfolded statement.
- `bit_false_le_bit_true : ∀ n, bit false n <= bit true n` — `le_succ
  (mul 2 n)`, accepted by defeq the same way.

**Measured `axiom_footprint`: empty**, both per-declaration
(`nat_axiom_inventory --require-axiom-free nat` exits 0, `nat: axiom=0
opaque=0 quotient=0 total_trusted=0`) and via
`every_nat_declaration_is_checked_and_axiom_free` (environment-derived
coverage, not a hand list — it failed once, naming exactly the five new
`Nat.bit*` names, before `definition_names`/`theorem_names` were updated).

**New facts created** (none flip an `F:ml430-*` mirror by hand, per the
standing rule): `F:nat-bit-false`, `F:nat-bit-true`, `F:nat-bit-true-pos`,
`F:nat-bit-false-le-bit-true`. The `F:ml430-nat-bitwise-bit-4c4b28a8` /
`land-bit` / `lor-bit` / `ldiff-bit` / `bitwise-comm` / `bitwise-swap`
mirror facts all also need `Nat.bitwise`/`Nat.land`/`Nat.lor`/`Nat.ldiff`,
none of which this lane declares, so they remain `open` — scoped out per
the brief, not a shortfall.

**Held-out check:** `natural-bitwise` (the `nat-bit`/`nat-bitwise`/`nat-bits`/
`nat-ldiff` family in `artifacts/autogenesis/nursery-v1.json`) is entirely
`development` partition, 19/19 entries verified by script before touching
anything. No held-out member was touched; none of the four new facts here
are nursery entries at all (they are new kernel-lean facts this lane
created, not existing nursery propositions).

**`nat_prelude` count:** before this lane, `the_build_is_deterministic`
pinned `73 + 369 = 442` (73 definitions, 369 theorems). After: `74 + 373 =
447` (one new definition, `Nat.bit`; four new theorems). Recomputed from the
test's own panic message (`left: 447`), never hand-incremented.

**Gates run:** `rustfmt --edition 2024 --check` on the three touched Rust
files (clean); `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` (clean, no new lint allowances needed); `cargo test
-p axeyum-lean-kernel --lib nat_prelude` (108 passed, 0 failed — up from 106
passed / 1 failed before the coverage-list update, plus one new concrete-
instantiation test with negative controls on every boundary theorem);
`python3 scripts/validate-facts.py` (1885 facts, 0 errors). `cargo check
-p axeyum-lean-kernel` also run standalone before the test suite.

**Not attempted, per scope:** `Nat.bitwise`, `Nat.bits`, `Nat.ldiff` — the
brief was explicit that landing `Nat.bit` alone is a complete success and
not to attempt all four. `Nat.bitwise` in particular needs a
`Bool -> Bool -> Bool` function argument threaded through a genuinely
structural-on-neither-argument recursion (fuel on both `m` and `n`
simultaneously, or a joint fuel), which is a substantially bigger
construction than anything in this lane.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise | `Nat.bit` (non-recursive, no fuel needed) plus `bit_false`/`bit_true`/`bit_true_pos`/`bit_false_le_bit_true`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-bit-*` facts; `Nat.bitwise`/`Nat.bits`/`Nat.ldiff` scoped out |
