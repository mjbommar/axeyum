# Notes: 215-nat-bitwise-2

Detail moved out of [`../status/215-nat-bitwise-2.md`](../status/215-nat-bitwise-2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Landed `nat_prelude/land.rs`**: `Nat.landAux`, `Nat.land`, plus four
theorems, all admitted on the first `Kernel::add_declaration` attempt:
- `land_zero_left : ∀ n, land 0 n = 0` — `Eq.refl` (fuel exhausted).
- `land_zero_right : ∀ m, land m 0 = 0` — induction on `m`, both cases
  `refl`.
- `land_one_one : land 1 1 = 1` — concrete, one fuel step, `Eq.refl`.
- `land_three_five : land 3 5 = 1` (`0b011 &&& 0b101 = 0b001`) — concrete,
  two fuel steps with genuinely DIFFERING bit patterns at each position, so
  it catches a wrong-way step (e.g. OR-shaped) that `land_one_one` alone —
  whose one bit matches on both operands — cannot distinguish.

`nat_prelude::nat_prelude_tests::land_computes_and_its_boundary_theorems_apply`
also checks 9 concrete `(m, n) -> land m n` pairs via `Kernel::def_eq`
(including `land 7 7 = 7`, a self-AND crossing several fuel steps), plus
negative controls on every theorem's inferred type (a wrong RHS value must
NOT `def_eq` the admitted statement) and on the raw computation (`land 3 5`
must not `def_eq` 5 or 7).

**Measured `axiom_footprint`**: empty. `nat_axiom_inventory
--require-axiom-free nat` exits 0: `nat: axiom=0 opaque=0 quotient=0
total_trusted=0` (the whole `nat` prelude, including `land`/`landAux`, over
its full `Kernel::environment()`, not a hand list).
`every_nat_declaration_is_checked_and_axiom_free` (environment-derived
coverage) also passes with the new names added to `definition_names`/
`theorem_names`.

**New facts created** (none flip an `F:ml430-*` mirror by hand, per the
standing rule — this prelude's `Nat.land` is a fresh construction, not
Mathlib's, and none of those facts' premises are established here):
`F:nat-land-zero-left`, `F:nat-land-zero-right`, `F:nat-land-one-one`,
`F:nat-land-three-five`. The `F:ml430-nat-land-bit-b9ab7475` / `land-comm` /
`land-assoc` mirror facts all additionally need `Nat.bitwise`/`Nat.bit`
composed with `land`/commutativity, none of which this lane declares, so
they remain `open`. `Nat.bitwise`/`Nat.lor`/`Nat.ldiff`/`Nat.bits` are
unattempted, per scope.

**Kernel rejections: none.** Every declaration in `land.rs` was admitted on
the first attempt — the only iteration was two Rust borrow-checker errors
(nested `f.foo(..., f.bar())` calls in the test file, per the standing
"flatten into sequential `let`s" note), fixed before ever calling
`cargo test`.

**Held-out / mutation check:** `natural-bitwise` (this family, in
`artifacts/autogenesis/nursery-v1.json`) is `development` partition, safe.
`scripts/fact-frontier.py` was run before touching anything; none of the
`F:ml430-nat-bitwise-*`/`land-*`/`lor-*` rows it lists carry a `⛔ HELD-OUT`
or `⛔ MUTATION` marker for anything this lane could reach (the two
`nat-clog`/`nat-sqrt`/`nat-log` HELD-OUT rows visible in that same BLOCKED
section belong to sibling families and were not touched). No nursery entry
was closed or flipped by this lane; all four new facts are fresh
kernel-lean facts, not nursery propositions.

**`nat_prelude` count:** before this lane (after merging `main`, which had
already landed `Nat.bit`/`Nat.descFactorial`/Bézout witnesses/primes-2/etc
since the earlier `207-nat-bitwise` lane's own before/after numbers),
`the_build_is_deterministic` pinned `75 + 395 = 470` (75 definitions, 395
theorems). After this lane: `77 + 399 = 476` (two new definitions,
`Nat.landAux`/`Nat.land`; four new theorems). Recomputed from the test's own
panic message (`left: 476`), never hand-incremented.

**Gates run:** `rustfmt --edition 2024` on the three touched Rust files
(clean, no diff); `cargo fmt --all --check` scoped to those files (clean);
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` (clean, no
new allowances); `cargo test -p axeyum-lean-kernel --lib nat_prelude` (110
passed, 0 failed — confirmed nonzero); `python3 scripts/validate-facts.py`
(1893 facts, 0 errors). `cargo check -p axeyum-lean-kernel` also run
standalone before the test suite.

**Not attempted, per scope:** `Nat.bitwise`, `Nat.lor`, `Nat.ldiff`,
`Nat.bits` — the brief explicitly allowed landing `Nat.land` alone as a
complete success once `Nat.bitwise` looked substantially bigger than a
single lane's construction.
