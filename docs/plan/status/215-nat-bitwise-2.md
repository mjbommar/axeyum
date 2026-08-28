# Lane: nat-bitwise-2 — land `Nat.land` (bitwise AND), directly, not through `Nat.bitwise`

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-bitwise-2, 2026-08-28).**

The frontier (per the prior `207-nat-bitwise` lane, which landed `Nat.bit`)
still had `Nat.bitwise`, `Nat.land`, `Nat.lor`, `Nat.ldiff`, `Nat.bits`
undeclared, blocking the `F:ml430-nat-bitwise-*`/`F:ml430-nat-land-*`/
`F:ml430-nat-lor-*`/`F:ml430-nat-ldiff-*` mirror facts. Per the brief, this
lane's target was one complete definition with boundary lemmas.

**`Nat.land` landed directly, NOT through a general `Nat.bitwise`.** Mathlib
routes `Nat.land := bitwise and`, and `Nat.bitwise` needs a `Bool -> Bool ->
Bool` function argument threaded through mismatched-length base cases
(`m=0`: `if f false true then n else 0`; `n=0`: `if f true false then m else
0`) — substantially more construction than a single lane's scope. `Nat.land`
needs none of that: each bit's AND is the `Nat` **product** of two values
already in `{0, 1}` (`Nat.mod _ 2`), so the recursive step is pure
arithmetic with no `Bool`/`cond` combinator at all — simpler than `Nat.bit`
needed to be.

**The fuel device WAS needed, and it is the exact shape `Nat.logAux`/
`Nat.testBitAux`/`Nat.sizeAux` already use**: structural `Nat.rec` on a fuel
argument, carrying `m`/`n` through and halving them (`Nat.div _ 2`) at each
step:

```
Nat.landAux 0        m n ≡ 0
Nat.landAux (succ f) m n ≡
  if n = 0 then 0
  else if m = 0 then 0
  else 2 * landAux f (m / 2) (n / 2) + (m % 2) * (n % 2)
Nat.land m n := Nat.landAux m m n
```

**The guard order is `n = 0` OUTERMOST**, the mirror of `log.rs`'s `b ≤ n`
ordering and for the identical reason: only the outermost cut collapses the
whole succ-step term with one rewrite, independent of the (possibly
symbolic) fuel predecessor. This makes `land m 0 = 0` an easy induction on
`m` where every step is `refl` with the induction hypothesis unused —
`log_zero_left`'s exact shape. `land 0 n = 0` is even cheaper: fuel is `m =
0`, so the outer `Nat.rec` is already exhausted and the theorem is `refl`
with no induction at all.

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

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise-2 | `Nat.land`/`Nat.landAux` (structural fuel recursion, direct — not through `Nat.bitwise`) plus `land_zero_left`/`land_zero_right`/`land_one_one`/`land_three_five`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-land-*` facts; `Nat.bitwise`/`Nat.lor`/`Nat.ldiff`/`Nat.bits` scoped out |
