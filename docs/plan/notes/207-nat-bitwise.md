# Notes: 207-nat-bitwise

Detail moved out of [`../status/207-nat-bitwise.md`](../status/207-nat-bitwise.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
