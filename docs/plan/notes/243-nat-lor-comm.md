# Notes: 243-nat-lor-comm

Detail moved out of [`../status/243-nat-lor-comm.md`](../status/243-nat-lor-comm.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `m = 0` case: closes via `lor_aux_zero_left_any_fuel` (LHS) + a plain
  `d.refl` (RHS, since the RHS's own `n = 0` argument is LITERAL and its
  outer guard fires directly regardless of the other operand's shape) — the
  same PATTERN `land`'s mirror case uses, just with `lor`'s own "any fuel"
  lemma and closing value (`b`, not `0`).
- `n = 0` case (nested, within the `m = succ` branch): exact mirror of the
  above, same pattern.
- Both nonzero: needs `lor_bit_comm` (`ble`-based max commutativity via
  `cases_mod_two`, four leaves, `d.refl` — the direct analogue of
  `bit_agreement`'s own construction) in place of `Nat.mul_comm`, PLUS the
  two `half_le_predecessor_of_succ` bounds `land`'s analogue never needed.
  This is the case that actually required new machinery, not just a
  parameter swap.
- Base case (`fuel = 0`, no case split): `land`'s closes by `refl` alone
  (both sides are the constant `0`). `lor`'s needs the `Le`-hypothesis
  derivation described above — this is the case the brief did not
  explicitly enumerate as one of "the four" but is where the extra
  hypotheses are most load-bearing.

**The trick that makes the both-nonzero case's `guarded(...)` scaffolding
work despite `lor`'s guards being VALUE-dependent (not constant like
`land`'s):** at `(succ_a, succ_b)` both guard checks (`beq(_, 0)`) reduce to
`false` regardless of which nonzero literal occupies which slot, so
`on_n_zero`/`on_m_zero` are dead code in this branch precisely as they are
for `land` — just for a different reason (`land`'s are dead because they're
constant either way; `lor`'s are dead because neither guard ever fires).
Verified by hand-tracing the reduction before writing the proof, not
assumed by analogy.

**Honest-flip criterion, checked against the Mathlib source already pinned
in the fact:** `F:ml430-nat-lor-comm-2666d7ef`'s own `formal.statement` reads
`n ||| m = m ||| n`, i.e. Mathlib's `Nat.lor`, which is `Nat.bitwise or` —
the SAME criterion `land_comm` used. Our `Nat.lor` is already proved equal
to the `bitwise or_fn` specialization by `Nat.bitwise_or_eq_lor`
(`nat_prelude/rec_agreement.rs`, landed by `nat-rec-agreement`), so this
closes the same function's commutativity, not a lookalike about a different
definition. Flipped via reconciliation evidence, exactly `land_comm`'s
route.

**Bonus task (bitwise_comm / bitwise_swap) — SIZED, NOT ATTEMPTED.**
`F:ml430-nat-bitwise-comm-1a273bae` needs `∀ {f}, (∀ b b', f b b' = f b' b) →
∀ n m, bitwise f n m = bitwise f m n` — a GENERIC commutativity over
`bitwiseAux` parameterized by an arbitrary commutative `f`, not a
specialization. `grep`ping `bitwise.rs` and `nat_prelude.rs` for
`bitwise_comm`/`bitwise_swap` found NOTHING — neither a declared name nor an
inline step, confirmed before sizing (not assumed from the brief). The
generic base case has the identical problem `lor`'s did (`bitwiseAux f 0 a b
= if f false true then b else 0`, order-dependent for a general `f`), so it
would need the same `Le`-hypothesis treatment PLUS threading `f`'s
commutativity hypothesis through the per-bit combine step (a `bit_agreement`
analogue that consumes the hypothesis rather than evaluating a concrete
`f`). `F:ml430-nat-bitwise-swap-7175e90e` additionally `depends_on
F:ml430-nat-bitwise-bit-4c4b28a8`, the `Nat.bit`-decode bridge that
`docs/plan/status/239-nat-fuel-transport.md` explicitly named as NOT
attempted for `land_bit`/`lor_bit`/`ldiff_bit` either. Both are
correctly-sized separate tasks, not a quick extension of this lane's work —
left open, not touched.

**Counts.** `nat_prelude` before this lane: 125 passed. After: 127 passed (2
new: `lor_comm_applies_at_a_concrete_discriminating_instance`, plus the
`every_nat_declaration_is_checked_and_axiom_free`/
`the_build_is_deterministic` inventory tests updated in place, not counted
as new). 2 new declarations, both theorems (`lor_aux_comm_of_fuel`,
`lor_comm`) — `the_build_is_deterministic`'s pin moved `88 + 452` → `88 +
454` (counted from the panic message's own mismatch, not hand-incremented).
`nat` trusted surface still `axiom=0 opaque=0 quotient=0`
(`nat_axiom_inventory --require-axiom-free nat`, run directly, printed
`ok: nat trusted surface = 0`). New fact `F:nat-lor-comm`;
`F:ml430-nat-lor-comm-2666d7ef` flipped open → proved via a reconciliation
evidence row. `python3 scripts/validate-facts.py`: 1926 facts, 0 errors.
`cargo fmt --all --check` (run as `rustfmt --edition 2024` on the touched
files, per this repo's shared-worktree rule) and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean.
NOT run: the aggregate `just check` / `./scripts/check.sh` (narrow lane run,
per repo convention — the coordinator re-runs the aggregate gate before
merging).

The 6 remaining `natural-bitwise` facts fuel-irrelevance was blocking:
`land_assoc`, `lor_assoc` (need a same-fuel ASSOCIATIVITY lemma, a 3-operand
case split, not a corollary of commutativity), `land_bit`, `lor_bit`,
`ldiff_bit` (need the `Nat.bit` decode bridge, not attempted by this or the
prior lane).
