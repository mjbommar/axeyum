# Lane: nat-lor — land `Nat.lor` (bitwise OR) following `Nat.land`'s fuel-recursion pattern

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-lor, 2026-08-28).** Landed `Nat.lor`/
`Nat.lorAux` in `nat_prelude/lor.rs`, following `land.rs`'s structural fuel
recursion (`Nat.rec` on the fuel argument), with two design deviations that do
not transfer unchanged from `Nat.land`:

- **Per-bit combinator**: `max (m%2) (n%2)` via the existing `Nat.ble` +
  `bool_select_nat`, not `a + b - a*b` (avoids a `Nat.sub` height dependency
  and its silent-truncation risk, even though truncation cannot actually
  trigger on bit-restricted inputs) and not a bespoke `Bool.rec` cut (more
  construction for the same result). OR of two `{0,1}` values is not their
  product, so `land`'s `mul` shortcut does not transfer at all.
- **Fuel-exhaustion base case**: `lorAux`'s `fuel = 0` row returns `n`, not
  the constant `0` `landAux` uses. Fuel stays `= m` (unchanged from `land`),
  which stays sound because whenever the outer `Nat.rec` on fuel truly
  reaches `0`, the repeatedly-halved `m`-argument is already `0` too (`m`
  always exceeds the `⌊log₂ m⌋ + 1` halvings needed to exhaust it) — but OR
  has no absorbing zero the way AND does, so the base case must return the
  other operand (`n`), not `0`. This is the part of "the shortcut does not
  transfer" that needed actually working out, not just the per-bit formula.
- **Guard order transferred unchanged**: `n = 0` checked OUTERMOST in
  `lorAux`'s succ case (mirrors `landAux`), and it is load-bearing for the
  same reason: `lor_zero_right`'s induction on `m` closes by `Eq.refl` at
  every step (no induction hypothesis forced), because the outermost
  `bool_select_nat` on `n_is_zero` selects the "return `m`" branch without
  forcing the untaken branch where the real recursive step lives.

Landed 3 boundary/sanity theorems (`lor_zero_left`, `lor_zero_right`,
`lor_three_five`), matching the "two or three boundary lemmas is a complete
success" scope. `lor_three_five = 7` is deliberately the same numeral pair as
`land_three_five = 1`, so the two proof terms differ only in the per-bit
combinator and their results are maximally distinguishing.

**Measured `axiom_footprint`**: empty for every new declaration (`Nat.lor`,
`Nat.lorAux`, and all three theorems), confirmed both by
`Kernel::axiom_footprint` in the dedicated test and by
`nat_axiom_inventory --require-axiom-free nat`, which after this lane still
reports `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`.

**Kernel rejected nothing in the final version.** The design reasoning above
(fuel-exhaustion base case, guard-branch returns) was worked out on paper
before construction, specifically because a naive fuel-`= m`-only translation
of `land`'s constant-`0` base case would have been WRONG for OR (would drop
all of `n`'s bits whenever `m = 0`) — this was caught by tracing the
recursion by hand before writing any kernel term, not by a kernel rejection.
Only friction during construction was Rust's borrow checker on nested
`d.foo(..., d.bar())` calls, flattened into sequential `let`s (the same
friction `land.rs`'s module doc reports for `Nat.land`).

**No HELD-OUT or MUTATION marker on any target.** Checked
`scripts/fact-frontier.py` for `F:ml430-nat-lor-assoc-82c4d0fd`,
`F:ml430-nat-lor-comm-2666d7ef`, `F:ml430-nat-lor-bit-a2f98c7c` (the Mathlib
mirror facts near this family) — none carry either marker. These mirror facts
were NOT flipped: this prelude's `Nat.lor` is a fresh construction, not
Mathlib's `bitwise and`-derived one, and their premises (general
`Nat.bitwise`) are not established here.

**`nat_prelude` test count**: 110 passed before this lane's edits (baseline,
same run as the merged-in `land`/bitwise work), 111 passed after (added
`lor_computes_or_and_its_boundary_theorems_apply`). `definition_names` +
`theorem_names` rendered count (`the_build_is_deterministic`'s pin, read off
its own panic message per the standing rule, never hand-counted): `476 -> 481`
(`77+399 -> 79+402`; +2 definitions `lorAux`/`lor`, +3 theorems
`lor_zero_left`/`lor_zero_right`/`lor_three_five`).

**Gates run**: `cargo check -p axeyum-lean-kernel --lib` clean;
`cargo test -p axeyum-lean-kernel --lib nat_prelude` 111 passed, 0 failed
(includes `every_nat_declaration_is_checked_and_axiom_free`, the
environment-derived coverage assertion, and `the_build_is_deterministic`);
`cargo fmt --all --check` clean; `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. Did not run the full workspace
`--features full` sweep or the aggregate `just check`/`check.sh` gate (out of
this lane's scope per the brief; the crate-scoped gates above are what the
brief asked for).

Out of scope, deliberately: `Nat.bitwise` (general two-argument form),
`Nat.ldiff`, `Nat.bits`/`Nat.lor` correctness theorems (commutativity,
associativity, the mirror `ml430-nat-lor-*` facts) — `lor` proved simple
enough that none of these were needed to land it, matching the brief's
"complete success" bar without extending scope.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-lor | `Nat.lor`/`Nat.lorAux` (fuel recursion, `max`-via-`ble` per-bit step, `n`-returning fuel base case) + 3 boundary theorems in `nat_prelude/lor.rs`; wired into `nat_prelude.rs`; `nat_prelude_tests.rs` coverage + dedicated test + pinned render count `476->481`; 3 new `F:nat-lor-*` facts |
