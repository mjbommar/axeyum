# Notes: 219-nat-lor

Detail moved out of [`../status/219-nat-lor.md`](../status/219-nat-lor.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
