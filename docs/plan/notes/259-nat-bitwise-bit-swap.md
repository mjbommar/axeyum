# Notes: 259-nat-bitwise-bit-swap

Detail moved out of [`../status/259-nat-bitwise-bit-swap.md`](../status/259-nat-bitwise-bit-swap.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. `bitwise_aux_swap_of_fuel : forall f fuel m n, Le m fuel -> Le n fuel ->
   Eq (bitwiseAux (swap f) fuel m n) (bitwiseAux f fuel n m)` -- fuel
   induction via the EXISTING `agree_by_fuel_induction`/`cases_zero_succ`
   skeleton (mirroring `bitwise_aux_comm_of_fuel`'s case-split tree
   exactly), but every base/boundary case closes by `d.refl` or a direct
   lemma application (`bitwise_aux_zero_left_any_fuel` instantiated at
   `swap f`) rather than by explicit `congr`+`trans` chaining through `hf`.
   Only the both-nonzero step needs `d.congr` over the induction
   hypothesis.
2. `bitwise_swap` -- assembled through the shared fuel `m + n`, reusing the
   ALREADY-DECLARED `bitwise_aux_agree_of_fuel` (from `bitwise_comm`'s own
   dispatch, called earlier in `nat_prelude.rs`), exactly as
   `bitwise_comm`'s own final assembly. No new fuel-irrelevance lemma
   needed -- it holds for ANY `f`, already proved generically.

Also added: `fst_fn` (`fun a b => a`, `#[cfg(test)]`-gated -- the
deliberately NON-commutative test fixture needed to discriminate this
statement, since `and`/`or`/`xor` are all commutative and could not catch a
vacuous "swap changes nothing" false positive), and `swap_fn` made
`pub(super)` (was already needed internally; widened so the test can build
`swap fst` directly).

### Verification

- Kernel accepted BOTH proof terms (`bitwise_aux_swap_of_fuel`,
  `bitwise_swap`) on the FIRST attempt -- no `TypeMismatch`/`UnboundFVar`
  iteration at all. The hand-derivation before writing Rust paid off
  directly; no debugging cycle was needed for the core construction.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- 140 passed, 0
  failed (was 139 before this lane per the brief).
- New test `bitwise_swap_applies_at_a_concrete_discriminating_instance`:
  symbolic restatement at a fixed concrete `f = fst_fn` (`fun a b => a`,
  non-commutative), concrete discriminating instance `bitwise(swap(fst), 5,
  3) = bitwise(fst, 3, 5) = 3`, with a non-vacuity check confirming the
  UNSWAPPED `bitwise(fst, 5, 3) = 5 != 3`. `and`/`or`/`xor` (all
  commutative) were deliberately NOT reused here, since a commutative `f`
  cannot discriminate a swap from a no-op.
- `every_nat_declaration_is_checked_and_axiom_free` -- required adding the
  two new names to `theorem_names` (caught immediately, as designed).
- `the_build_is_deterministic` -- pin moved `93 + 489` -> `93 + 491` (2 new
  theorems, 0 new definitions), taken from the panic's own mismatch
  (`left: 584`), not hand-incremented.
- **Pre-existing merge artifact found and fixed, unrelated to this lane's
  own work but blocking its `clippy -D warnings` gate**: a "TWO LANES
  ADDING FUNCTIONS TO ONE RUST FILE" hunk-boundary defect (CLAUDE.md's
  Gotchas) had left `clog_computes_and_its_boundary_equations_apply`'s doc
  comment and `#[test]` attribute duplicated onto
  `land_bit_applies_at_a_concrete_discriminating_instance` immediately
  below it, leaving the `clog` test itself silently uncompiled dead code
  (present in the tree since the merge with `main` at the start of this
  session, well before this lane touched anything -- confirmed via `git
  show` on the pre-lane commit). Fixed by moving the doc comment and
  `#[test]` to their own function; `clog_computes_and_its_boundary_equations_apply`
  now runs as its own test (confirmed passing) and the duplicate-attribute
  clippy error is gone.
- `cargo fmt --edition 2024` (per-file) and
  `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
  clean.
- `python3 scripts/validate-facts.py` -- 0 errors (1935 facts checked).
- Both new fact `checker_command`s run and confirmed exit 0: the
  `nat_theorem_inventory`/`grep -Ec` anchor (count 1), the concrete
  discriminating-instance test (`cargo test ... bitwise_swap_applies_...`,
  1 passed), and `nat_axiom_inventory --require-axiom-free nat` (prints
  `ok: nat trusted surface = 0`).
- `scripts/gen-autogenesis-bitwise-family-projection.py` checked for a
  pin on either target fact's `epistemic_status` -- it only names
  `F:ml430-nat-testbit-{land,lor,ldiff}-*`, unrelated to `bitwise_swap`/
  `bitwise_bit'`, so no conflict.

### Facts closed

- `F:nat-bitwise-swap` -- NEW native fact, `proved`, `kernel-lean` route,
  `axiom_footprint: []`. `formal.statement` is `nat_theorem_inventory`'s
  `render_lean` output verbatim (paste, not transcription).
- `F:ml430-nat-bitwise-swap-7175e90e` -- flipped `open -> proved` via
  reconciliation with `F:nat-bitwise-swap`. Checked the mirror-flip
  criterion first: our `Nat.bitwise` genuinely IS Mathlib's own general
  combinator (established for `bitwise_comm` already, and unchanged here),
  so this is an honest flip in the strongest sense -- restated pointwise
  because this kernel has no `funext` to state Mathlib's
  `Function.swap`-level function equality directly (the same restatement
  convention used elsewhere in this prelude, e.g. `nat_prelude/cantor.rs`).
  Note: this fact's OWN proof route does not go through
  `F:ml430-nat-bitwise-bit-4c4b28a8` (its `depends_on` edge), which remains
  open -- `depends_on` is curriculum/leakage metadata only and grants no
  proof authority, consistent with the standing convention.

## `bitwise_bit'`: what it would still need (not attempted)

`Nat.bitwise_bit' : forall {f} (a : Bool) (m : Nat) (b : Bool) (n : Nat),
(m = 0 -> a = true) -> (n = 0 -> b = true) -> bitwise f (bit a m) (bit b n)
= bit (f a b) (bitwise f m n)`. This needs the SAME fuel-swap machinery
`bit_decode.rs`'s `land_bit` built (choosing an artificially `succ`-shaped
fuel via `bit a m`'s own shape, decoding the raw `div`/`mod` subterms via
`bit_div_two`/`bit_mod_two`, swapping back), but generalized over a
symbolic `f` -- meaning the per-bit combine and the two boundary-guard
resolutions will need `bitwise`'s own general machinery (this file's
`bitwise_aux_zero_left_any_fuel`/`bool_select_same`-shaped reasoning)
rather than `land`'s absorbing-zero shortcut. The two side hypotheses
(`m = 0 -> a = true`, `n = 0 -> b = true`) exist specifically to rule out
the leading-zero ambiguity the GENERAL `bitwise` recursion has that
`land`/`lor`/`ldiff`'s own specializations do not (per
`docs/plan/status/251-nat-bit-decode.md`'s own note that this theorem is
"not a shortcut" to `lor_bit`/`ldiff_bit`). Whoever picks this up next
should re-verify `bit_decode.rs`'s current state directly rather than
trusting this paragraph, per CLAUDE.md's standing warning that a
second-hand sizing claim can be stale.

## Commits (this lane, `nat-bitwise-bit-swap`)

Run `git log --oneline` on this branch for exact SHAs; recorded in the
session's final report.
