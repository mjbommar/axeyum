# Notes: 256-nat-bitwise-comm

Detail moved out of [`../status/256-nat-bitwise-comm.md`](../status/256-nat-bitwise-comm.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **The per-bit combine** (expected). `bitwiseAux`'s successor row combines
   `f (beq (m%2) 1) (beq (n%2) 1)` into a `Nat` via `bool_select_nat`. Since
   `hf (beq (m%2) 1) (beq (n%2) 1) : Eq Bool (f a b) (f b a)` directly IS the
   swapped equality at those two concrete-shaped-but-symbolic-valued `Bool`
   terms, no case split is needed (unlike `bit_agreement`/`lor_bit_comm`,
   which case-split on `m % 2`/`n % 2` because their `f` is concrete). That
   `Bool` equality is lifted into a `Nat` equality (the two
   `bool_select_nat` applications) via a small `congr_bool_to_nat` helper
   (`bitwise.rs`) built from `ops.rs`'s ALREADY-GENERIC
   `NatOps::bool_eq_motive`/`NatOps::bool_transport` -- a first pass
   reinvented `Eq.{1} Bool` and the raw `Eq.rec` application by hand before
   noticing `ops.rs` already carries the whole
   `bool_eq`/`bool_refl`/`bool_transport`/`bool_eq_motive`/`bool_symm`/
   `bool_trans` family (built originally for `false_true_elim`). Exactly
   the "search for the STEP, not the NAME" trap CLAUDE.md's Gotchas
   describes -- caught only because the duplicate `d.refl` (hardcoded to
   `Nat`) produced a `TypeMismatch` on a `Bool`-typed term
   (`expected: AxNat, got: (fun x0:Bool => Bool) Bool.false`), which is the
   "sort error wearing a TypeMismatch's clothes" pattern from the same file.
2. **The `m = 0`/`n = 0` boundary** (NOT anticipated going in). For `land`/
   `lor` (concrete `f`), the two boundary rows (`f false true`-conditioned
   and `f true false`-conditioned) evaluate to the SAME literal on both
   sides trivially. For a SYMBOLIC `f` they are two genuinely different
   partial applications, equal only via `hf true false`/`hf false true`.
   `declare_bitwise_aux_comm_of_fuel`'s two single-zero branches (`a = 0`,
   `b = 0`) each need one `congr_bool_to_nat` call over `hf` at the
   boundary literals -- this is the "genuinely new proof content beyond
   `lor_aux_comm_of_fuel`'s transport" CLAUDE.md's own fact-registration
   guidance anticipated.

### The four lemmas landed (`nat_prelude/bitwise.rs`, uncontended)

1. `bitwise_aux_zero_left_any_fuel : forall f fuel n, Eq (bitwiseAux f fuel
   0 n) (bool_select_nat (f false true) n 0)` -- unconditional in `f`, no
   `hf` needed (structural, mirrors `land`/`lor`'s `_zero_left_any_fuel`,
   with `lor`'s extra nested `cases_zero_succ` on `n` since the fuel-exhaustion
   value is not the constant `0`).
2. `bitwise_aux_agree_of_fuel` (double-fuel induction via
   `agree_by_double_fuel_induction`) -- no `hf` needed: fuel-irrelevance
   never swaps the value arguments. The succ-step's guard values
   (`on_n_zero`/`on_m_zero`) are the REAL `bitwiseAux` formulas
   (`bool_select_nat (f true false) ...`/`bool_select_nat (f false true)
   ...`), not placeholders -- `n` stays symbolic in this lemma, so the
   guard never reduces and a placeholder would fail to be defeq to the
   actual unfolding.
3. `bitwise_aux_comm_of_fuel : forall f, (forall a b, f a b = f b a) ->
   forall fuel m n, Le m fuel -> Le n fuel -> Eq (bitwiseAux f fuel m n)
   (bitwiseAux f fuel n m)` -- the both-nonzero step's guard values ARE
   placeholders (`succ_a`, `succ_b` themselves), because BOTH
   `beq(succ_a, 0)` and `beq(succ_b, 0)` reduce to the literal `false`
   regardless of what sits in the discarded branch -- `lor_aux_comm_of_fuel`'s
   own precedent, and the opposite of (2)'s situation.
4. `bitwise_comm` -- assembled through the shared fuel `m + n`, exactly as
   `land_comm`/`lor_comm`.

`half_le_predecessor_of_succ` (`rec_agreement.rs`, fully generic Nat
arithmetic, previously private) was widened to `pub(super)` -- a two-line,
visibility-only diff -- rather than duplicating ~40 lines of arithmetic a
fifth time.

### Verification

- Kernel accepted all four proof terms on the FIRST attempt (no
  `TypeMismatch`/`UnboundFVar` iteration on the core construction --
  the borrow-checker errors and the test-helper `d.refl`/duplicate-`bool_eq`
  bugs described above were the only issues, both outside the kernel
  proof terms themselves).
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- 133 passed, 0
  failed (was 132 before this lane; +1 from the new concrete test).
- New test `bitwise_comm_applies_at_a_concrete_discriminating_instance`:
  symbolic restatement at a fixed concrete `f = xor_fn` (with a
  from-scratch `hf` proof for `xor` built by a four-leaf `Bool.rec` case
  split, `bool_fn_comm`), concrete discriminating instance
  `bitwise(xor, 3, 5) = bitwise(xor, 5, 3) = 6`, and a negative control at
  `f = or_fn`, insufficient fuel `(0, 0, 1)` confirming
  `bitwiseAux(or, 0, 0, 1) = 1 != 0 = bitwiseAux(or, 0, 1, 0)` -- the same
  witness the Python simulation used, NOT copied from `lor`'s own control
  (which is `(1, 3, 4)`/`(1, 7, 7)`-shaped, for a different lemma).
- `every_nat_declaration_is_checked_and_axiom_free` -- required adding the
  four new names to `theorem_names` (the environment-derived coverage
  assertion caught the omission immediately, exactly as designed).
- `the_build_is_deterministic` -- pin moved `89 + 463` -> `89 + 467` (4 new
  theorems, 0 new definitions), taken from the panic's own mismatch
  (`left: 556`), not hand-incremented.
- `cargo fmt --edition 2024` (per-file) and
  `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
  clean.
- `python3 scripts/validate-facts.py` -- 0 errors (1930 facts checked).
- Both fact `checker_command`s run and confirmed exit 0: the
  `nat_theorem_inventory`/`grep -Ec` anchor (count 1) and
  `nat_axiom_inventory --require-axiom-free nat` (prints
  `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`).

### Facts closed

- `F:nat-bitwise-comm` -- NEW native fact, `proved`, `kernel-lean` route,
  `axiom_footprint: []`. `formal.statement` is `nat_theorem_inventory`'s
  `render_lean` output verbatim (paste, not transcription).
- `F:ml430-nat-bitwise-comm-1a273bae` -- flipped `open -> proved` via
  reconciliation with `F:nat-bitwise-comm`. Checked the mirror-flip
  criterion first: unlike `land_comm`/`lor_comm` (which needed a DIFFERENT
  route than Mathlib's own `bitwise_comm`, since `land`/`lor` are hand-rolled
  fuel recursions, not `bitwise` specializations, at proof-construction
  time), this fact's native proof genuinely IS Mathlib's own general
  `Nat.bitwise` combinator -- an honest flip in the strongest sense: same
  `def`, same theorem, modulo the cosmetic `n m`/`m n` argument-name order.

## `lt_xor_cases`: what it still needs (not attempted)

The lane that built `Nat.xor` (`docs/plan/status/253-nat-xor-parity.md`)
sized this as needing a **highest-differing-bit induction** -- unrelated in
size to defining `xor` itself. I did not open that file or investigate
further; per the brief, `bitwise_comm` was the priority and "landing
`bitwise_comm` alone is a good outcome." Whoever picks this up next should
re-read `docs/plan/status/253-nat-xor-parity.md` directly rather than
trusting this paragraph (per CLAUDE.md's own repeated warning that a
second-hand sizing claim can be stale) and verify `Nat.xor`/its bit-decode
lemmas (`xor.rs`, `bit_decode.rs`) are still exactly as described before
budgeting the induction.

## Commits (this lane, `nat-bitwise-comm`)

1. `wip(nat): bitwise_comm -- Python simulation confirms Le-hypothesis shape`
   -- plan only, no code.
2. `wip(nat): bitwise_comm -- compiles, kernel acceptance not yet verified`
   -- the four lemmas + `nat_prelude.rs` wiring + `half_le_predecessor_of_succ`
   visibility change.
3. (this commit) -- test-inventory registration, pin fix, concrete
   discriminating test, `congr_bool_to_nat`/`bool_eq` deduplication against
   `ops.rs`'s existing `Bool`-`Eq` family, fact ledger updates, this status
   file.

Run `git log --oneline` on this branch for exact SHAs.
