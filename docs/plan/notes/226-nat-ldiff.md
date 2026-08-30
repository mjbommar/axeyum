# Notes: 226-nat-ldiff

Detail moved out of [`../status/226-nat-ldiff.md`](../status/226-nat-ldiff.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Fuel-exhaustion base case takes `land`'s shape, not `lor`'s.** Fuel is
  sized `= m` (unchanged), and `land.rs`/`lor.rs` both establish that by the
  time the outer `Nat.rec` on fuel genuinely reaches `0`, the current
  `m`-argument at that call is always definitionally `0` (fuel decrements by
  `1` per step while `m` at least halves per step, and halving `m` times
  always reaches `0` in at most `m` halvings for `m >= 1`). For `land`, `m`
  carries the absorbing zero, so the base case can ignore both leftover
  arguments and return the constant `0`. For `ldiff`, `m` — the SAME operand
  the fuel is sized against — is *also* the absorbing-zero operand, so the
  identical reasoning applies for the identical reason: `ldiffAux 0 m n := 0`,
  land's shape exactly, not lor's `n`-returning fix (which was needed there
  only because `lor`'s fuel-sized operand carries NO absorbing zero).
- **The inner succ-row guard is a genuine hybrid of both siblings**, because
  its two zero-checks protect two operands with different absorbing
  behaviour: `n = 0` returns `m` unchanged (`lor`'s shape — no absorbing zero
  on this side), `m = 0` returns `0` (`land`'s shape — absorbing zero here).
- **Per-bit combinator**: neither `land`'s product nor `lor`'s `max` (via
  `Nat.ble`) — `bitLdiff a b := if b = 0 then a else 0`, built from
  `Nat.beq`/`bool_select_nat`, already load-bearing in this same term for the
  zero-guards. No new primitive or height dependency.
- **Guard order unchanged**: `n = 0` OUTERMOST in `ldiffAux`'s succ case
  (mirrors `land`/`lor`), load-bearing for the identical proof-cost reason:
  `ldiff_zero_right`'s induction on `m` closes by `Eq.refl` at every step (no
  induction hypothesis forced), because the outermost `bool_select_nat` on
  `n_is_zero` selects the "return `m`" branch without forcing the untaken
  branch where the `m = 0` test and the real recursive step live.

Landed 4 boundary/sanity theorems (`ldiff_zero_left`, `ldiff_zero_right`,
`ldiff_three_five`, `ldiff_five_three`) — one more than the "two or three is a
complete success" floor, because `ldiff`'s non-commutativity gives it a
negative control `land`/`lor` cannot express at all: `ldiff_three_five`
(`ldiff 3 5 = 2`) and `ldiff_five_three` (`ldiff 5 3 = 4`) are the SAME two
operands swapped, producing a DIFFERENT answer. The evaluation test
(`ldiff_computes_and_its_boundary_theorems_apply`) checks this both by
`Kernel::def_eq` over a ten-row concrete table (including `(3,5)->2` and
`(5,3)->4` side by side) and by a dedicated negative control asserting
`ldiff_five_three`'s statement must NOT `def_eq` `Eq (ldiff 5 3) 2` — the
value its swapped sibling gives.

**Measured `axiom_footprint`**: empty for every new declaration (`Nat.ldiff`,
`Nat.ldiffAux`, and all four theorems), confirmed both by
`Kernel::axiom_footprint` in the dedicated test and by
`nat_axiom_inventory --require-axiom-free nat`, which after this lane still
reports `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`.

**Kernel rejected nothing in the final version.** The design reasoning above
(which sibling's base case applies, which sibling's guard-branch shape
applies to each zero-check) was worked out on paper before construction,
specifically because copying `land`'s base case without checking which
operand carries the absorbing zero could have looked plausible and been
wrong for a definition with an ASYMMETRIC absorbing zero — this was avoided
by tracing the recursion by hand first, not by a kernel rejection. Two clippy
`doc_markdown` findings (bare `ANDing` in the module doc, wanting backticks)
were the only friction, caught by `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` and fixed before the final commit.

**No HELD-OUT or MUTATION marker on any target.** Checked
`scripts/fact-frontier.py` for `F:ml430-nat-ldiff-bit-6be49bb8` (the Mathlib
mirror fact near this family, plus the `nat-testbit-ldiff` mirror fact) —
neither carries either marker, though `nat-testbit-ldiff` is flagged as
possibly load-bearing for `gen-autogenesis-bitwise-family-projection.py` and
was left untouched regardless (out of scope: this lane creates new
`F:nat-ldiff-*` facts only). Neither mirror fact was flipped: this prelude's
`Nat.ldiff` is a fresh construction, not Mathlib's `bitwise`-derived one, and
its premise (general `Nat.bitwise`) is not established here.

**`nat_prelude` test count**: 92 passed on a targeted filtered run before this
lane's test additions (baseline, same run as the merged-in `land`/`lor`/
bitwise work), 114 passed after on the full `nat_prelude` filter (adds
`ldiff_computes_and_its_boundary_theorems_apply`; the wider post-count also
picks up `shape_index`/`string_prelude` tests matched by the same substring
filter, so the two numbers are not directly subtracted). `definition_names` +
`theorem_names` rendered count (`the_build_is_deterministic`'s pin, read off
its own panic message per the standing rule, never hand-counted):
`492 -> 498` (`81+411 -> 83+415`; +2 definitions `ldiffAux`/`ldiff`, +4
theorems `ldiff_zero_left`/`ldiff_zero_right`/`ldiff_three_five`/
`ldiff_five_three`).

**Gates run**: `cargo check -p axeyum-lean-kernel` clean; `cargo check -p
axeyum-lean-kernel --tests` clean; `cargo test -p axeyum-lean-kernel --lib
nat_prelude` 114 passed, 0 failed (includes
`every_nat_declaration_is_checked_and_axiom_free`, the environment-derived
coverage assertion, and `the_build_is_deterministic`); `cargo fmt --all
--check` clean; `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` clean; `scripts/validate-facts.py` 1908 facts checked
(including the 4 new ones), 0 errors; all four new facts' `checker_command`s
(the `nat_theorem_inventory` anchored-grep for each theorem name, and
`nat_axiom_inventory --require-axiom-free nat`) run and confirmed to pass.
Did not run the full workspace `--features full` sweep or the aggregate
`just check`/`check.sh` gate (out of this lane's scope per the brief; the
crate-scoped gates above are what the brief asked for).

Out of scope, deliberately: `Nat.bitwise` (general two-argument form),
`Nat.bits`, `Nat.ldiff` correctness theorems beyond the four boundary/sanity
ones (the `ml430-nat-ldiff-*`/`ml430-nat-testbit-ldiff-*` mirror facts) —
`ldiff` proved simple enough that none of these were needed to land it,
matching the brief's "complete success" bar without extending scope.
