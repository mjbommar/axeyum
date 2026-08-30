# Notes: 282-int-parity-two

Detail moved out of [`../status/282-int-parity-two.md`](../status/282-int-parity-two.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `Int.emod_two_ne_zero` (`F:ml430-int-emod-two-ne-zero-d07d008f`),
  `Int.emod_two_ne_one` (`F:ml430-int-emod-two-ne-one-5b930333`) — pure `n % 2`
  facts, no `Even`/`Odd` at all. Built from a new internal (non-mirror) helper
  `Int.emod_two_eq_zero_or_one` — `Int.rec` on `n`, `Nat.mod_two_eq_zero_or_one`
  on the bound `Nat` field of each branch, `nat_eq_to_int` lifting each `Nat`
  disjunct across (the `ofNat` branch is a straight lift; the `negSucc` branch
  lifts through `fun x => subNatNat 2 (succ x)`, which is where the sign flip
  between `m`'s parity and `negSucc m`'s parity shows up) — then `Or.elim` plus
  a small `0 ≠ 1 : Int` refutation (`zero_lt_one` rewritten to `Lt one one` via
  `Eq.rec`, refuted by `lt_irrefl`).
- `Int.ediv_two_mul_two_of_even` (`F:...-0095e2a6`),
  `Int.ediv_two_mul_two_add_one_of_odd` (`F:...-a7ec30d7`),
  `Int.add_one_ediv_two_mul_two_of_odd` (`F:...-3c9ef32f`) — from
  `Int.ediv_add_emod` at `b := 2`, rewriting `emod n 2` via two new
  case-split helpers (`even_implies_emod_zero`/`odd_implies_emod_one`, same
  shape as `emod_two_eq_zero_or_one` but hypothesis-carrying — the `negSucc`
  branch of the EVEN one needs a contrapositive through
  `Nat.even_iff_odd_succ`, since that lemma relates `Even m` to `Odd (succ m)`,
  not `Even (succ m)` to `Odd m`; the ODD one's `negSucc` branch reads the same
  lemma directly, no contrapositive needed), then `add_zero`/`mul_comm`/
  `add_comm` to reshape. The `add_one_...` fact shares its derivation with
  `ediv_two_mul_two_add_one_of_odd` via a private helper rather than
  re-deriving it.
- `Int.odd_of_mul_left` (`F:...-b580971e`), `Int.odd_of_mul_right`
  (`F:...-d6d1fc1d`) — route entirely through `Int.natAbs` being
  multiplicative (`nat_abs_mul`, `gcd.rs`), so **no `Int.rec` at all**: sign
  cancels out of the argument completely. Contrapositive on the `Nat` side:
  `Even a -> Even (a*b)` (two new helpers, `nat_even_mul_of_even_left`/
  `_right`, via `Nat.right_distrib`/`left_distrib` — existentially witnessed,
  `Exists.rec`-eliminating the `Even` hypothesis) plus `Nat.even_not_odd`
  refutes the negation; a new helper `nat_not_even_implies_odd`
  (contrapositive of `Nat.even_or_odd_exists`) closes it.

**Left open (not attempted — a genuinely separate-sized task):**

- `F:ml430-int-even-add-3c4536e3` — `Even (m+n) <-> (Even m <-> Even n)`.
- `F:ml430-int-even-add-bc8e1394` — `Even (m+n) <-> (Odd m <-> Odd n)` (this
  is Mathlib's `Int.even_add'`, a DIFFERENT proposition from the one above
  despite the brief's warning that both facts share the Mathlib base name
  `even_add` — confirmed by reading `Mathlib/Algebra/Group/Int/Even.lean`
  (`even_add`) and `Mathlib/Algebra/Ring/Int/Parity.lean` (`even_add'`)
  directly).
- `F:ml430-int-even-add-one-af33da18` — `Even (n+1) <-> Not (Even n)`.

All three need an additive compatibility law for `emod` — `(m+n) % 2` in
terms of `m % 2`/`n % 2`, or equivalently the `negSucc` branch of `Int.add`
interacting with parity — that does not exist yet in any branch-free form.
This is NOT the same machinery as the division-by-two family above (that
needed only `Int.rec` + a fixed `Nat` lemma per branch; addition's branch
table over TWO `Int.rec` splits, each contributing sign information, is a
different and larger shape). Estimate: comparable in size to everything
landed in this lane combined, not a quick follow-on.

Every Nat-level helper built for this lane
(`nat_even_predicate`/`nat_even_mul_of_even_left`/`_right`/
`nat_not_even_implies_odd`/`nat_even_succ_implies_odd`) is module-private to
`int_prelude/parity.rs`, NOT added to `nat_prelude` (out of this lane's scope
per the brief) — a future lane building `Nat.Even.mul_left`/`Nat.odd_mul`
style theorems in `nat_prelude/parity.rs` could supersede these with real
public `Nat` lemmas and simplify this file's `odd_of_mul_*` proofs, but
nothing here depends on that happening.

Checks run: `cargo test -p axeyum-lean-kernel --lib int_prelude::` (49
passed), `cargo fmt --all --check` clean, `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean, `python3
scripts/check-test-attribute-integrity.py` (0 findings — touched
`int_prelude_tests.rs`'s `derived_laws` pin, recounted via
`scripts/recount-pinned-inventory.py`, not incremented), `python3
scripts/validate-facts.py` (0 errors, 2034 facts). Each closed fact's two
evidence rows (`cargo test … int_prelude::` and a per-theorem
`theorem_axiom_footprint` grep) were run and separately confirmed to FAIL on
a mutated/nonexistent theorem name before being written into the ledger.

Commits: `c75478ad7` (the eight kernel theorems), `05cc46135` (the seven
fact-ledger flips). Not pushed.

Next lane: the three `even_add*` facts above, or continue the division-by-two
family's pattern into other `ml430-int-*` mirrors not yet dispatched.
