# Notes: 262-nat-bitwise-bit-prime

Detail moved out of [`../status/262-nat-bitwise-bit-prime.md`](../status/262-nat-bitwise-bit-prime.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **The per-bit combine needs an extra round-trip.** `bitwiseAux`'s general
   step converts each raw `Nat.mod _ 2` bit to `Bool` via `beq _ 1` (this
   file's ad hoc `bodd`) before applying `f`, while `Nat.bit_mod_two` decodes
   the SAME raw `mod` term to `bool_select_nat test 1 0`. These two encodings
   don't syntactically match, so a new lemma, `cond_beq_one_eq_self : Eq Bool
   (beq (bool_select_nat x 1 0) 1) x`, closes the gap (two-leaf `Bool` split,
   both branches `refl` since `beq 1 1`/`beq 0 1` compute on small literals).
   `land`/`lor`/`ldiff`'s own combines never round-trip through `Bool` (they
   stay in `{0,1} : Nat` throughout), so this step has no analogue in
   `bit_decode.rs`.
2. **The two side hypotheses are load-bearing, not decoration.** Simulated
   before writing any Rust (per the standing rule): `bitwiseAux`'s `n = 0`
   boundary row returns the WHOLE bit-encoded operand `bit a m`, not a
   per-operator absorbing constant -- so at `a = false, m = 0` a misbehaved
   `f` (the constant-`true` function is the working counterexample) makes the
   UNCONDITIONAL claim false. The hypotheses rule out exactly this
   leading-zero encoding.

**Discharging the hypotheses needed one new technique beyond anything
`land_bit`/`lor_bit`/`ldiff_bit` used**: a "generalize with equality" case
split (`cases_zero_succ_with_eq`, new, local to `bitwise.rs`), following
`cases_zero_succ`'s own doc verbatim ("a caller wanting a hypothesis usable
inside a branch must fold it into `motive` and re-introduce it per branch").
`hm`/`hn`'s conclusions are folded through the OUTER `a`/`b` case splits using
each branch's own literal (so no separate "remember" is needed for `a`/`b`
themselves), and `cases_zero_succ_with_eq` recovers `Eq m 0`/`Eq n 0` (for the
ORIGINAL fvar, not a substituted literal) at exactly the leaf that needs it,
via `Nat.eq`-generalization built from `NatOps::eq_motive`/`transport`'s
existing pattern applied to `cases_zero_succ`. `NatOps::false_true_elim`
closes the contradiction once both pieces combine to `Eq Bool false true`.

Six leaves total in the guard-resolution tree (split `b`, then within
`b=false` split `n`; within either `b`-branch, split `a`, then within `a =
false` split `m`): two close via `false_true_elim` (the `n=0` leaf under
`b=false`, the `m=0` leaf under `a=false`), the other four close by pure
`refl` (the guards resolve false by defeq alone, since `bit true k` is
`succ`-shaped for ANY `k` and `bit false (succ k)` reduces succ-shaped too --
both established by `bit_decode.rs`'s own module doc).

## Verification

- **Kernel accepted the proof term on the FIRST attempt** -- no
  `TypeMismatch`/`UnboundFVar` iteration. The hand-derivation (Python-free
  here; small enough to reason through directly, matching `bitwise_swap`'s
  own experience) paid off directly.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- 145 passed, 0
  failed (was 144 before this lane).
- New test `bitwise_bit_applies_at_a_concrete_discriminating_instance`: `f :=
  fst` (the same deliberately non-commutative fixture `bitwise_swap`'s test
  uses) at `a = false, m = 2, b = true, n = 3`. `a != b` catches an
  argument-order bug in the per-bit combine; `m = 2` (nonzero) exercises the
  leaf that must DISCHARGE `hm` even though its premise never fires (built via
  `Nat.succ_ne_zero` + `False.rec`, the exact pattern
  `zero_or_succ_applies_at_a_compound_term_and_is_consumed_by_or_elim`'s
  `left_branch` already uses); `b = true` keeps `hn` trivial. Both sides
  compute to `4`; a non-vacuity check confirms the swapped combine computes to
  `5`, so the instance genuinely discriminates.
- `every_nat_declaration_is_checked_and_axiom_free` -- required adding
  `p.bitwise_bit` to `theorem_names` (caught immediately, as designed).
- `the_build_is_deterministic` -- pin moved `93 + 495` -> `93 + 496` (1 new
  theorem, 0 new definitions), taken from the panic's own mismatch (`left:
  589`), not hand-incremented.
- `cargo fmt --edition 2024` (per-file) and `cargo clippy -p axeyum-lean-kernel
  --all-targets -- -D warnings` both clean. Three new functions
  (`bitwise_bit_goal`, `bitwise_guard_inner`, `resolve_bitwise_bit_guard`)
  needed `#[allow(clippy::too_many_arguments)]`, matching the existing
  precedent on `NatOps::bezout` in `ops.rs`.
- `python3 scripts/validate-facts.py` -- 1938 facts, 0 errors.
- Both new fact `checker_command`s run and confirmed exit 0: the
  `nat_theorem_inventory`/`grep -Ec` anchor (count 1, quoting verified with
  `/usr/bin/grep` explicitly per this repo's ugrep-vs-grep warning -- the
  pattern needs a literal trailing apostrophe, handled via `'\''`), the
  concrete discriminating-instance test (1 passed), and
  `nat_axiom_inventory --require-axiom-free nat` (prints `ok: nat trusted
  surface = 0`).
- `scripts/gen-autogenesis-bitwise-family-projection.py`'s `MAPPINGS` checked
  for a pin on this fact's `epistemic_status` -- it only names three unrelated
  `F:ml430-nat-testbit-{land,lor,ldiff}-*` facts, so no conflict.

### Files touched

- `crates/axeyum-lean-kernel/src/nat_prelude/bitwise.rs` -- all new
  construction (`cond_beq_one_eq_self`, `bitwise_bit_combine`,
  `bitwise_bit_stepped`, `bitwise_bit_goal`, `cases_zero_succ_with_eq`,
  `bitwise_guard_inner`, `resolve_bitwise_bit_guard`, `declare_bitwise_bit`).
- `crates/axeyum-lean-kernel/src/nat_prelude/bit_decode.rs` -- ONE line:
  `case_bool` made `pub(super)` so `bitwise.rs` could reuse it instead of
  building a third local copy (both files are this lane's; `rec_agreement.rs`
  and the other off-limits files were not touched).
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` -- new `bitwise_bit: NameId`
  field, its `kernel.name_str(nat, "bitwise_bit'")` init (note the literal
  apostrophe in the STRING, matching Mathlib's own spelling -- precedented by
  `congrFun'` in `prelude.rs`), and the dispatch call placed right after
  `declare_bit_decode_all` (needs both that and `declare_bitwise_comm`, both
  earlier in the same function).
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` -- added
  `p.bitwise_bit` to `theorem_names`, the new concrete test, and the pin bump.
- `artifacts/facts/F-nat-bitwise-bit.json` (new) and
  `artifacts/facts/F-ml430-nat-bitwise-bit-4c4b28a8.json` (open -> proved).

## Mirror-flip honesty

Checked rather than assumed, per the standing rule: our `Nat.bitwise` genuinely
IS Mathlib's own general combinator (established for `bitwise_comm`/
`bitwise_swap` already, unchanged here), and unlike the `testBit`-shaped
siblings the family-projection script pins open (Mathlib's `testBit` returns
`Bool` against our `Nat` -- an unflippable codomain mismatch), `bitwise_bit'`'s
codomain is `Nat` throughout on BOTH sides of the equation. So this flip is
honest in the strongest sense the criterion recognizes: same functions, same
theorem, restated with our own binder/hypothesis shape (which happens to match
Mathlib's statement verbatim here -- no `funext`-avoiding restatement was
needed, unlike `bitwise_swap`).

## Commits (this lane, `nat-bitwise-bit-prime`)

Run `git log --oneline` on this branch for exact SHAs; recorded in the
session's final report. Four commits: an early uncompiled checkpoint, the
working construction + test + pin, the fact-ledger closing, and this status
file.
