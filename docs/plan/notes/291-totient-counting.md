# Notes: 291-totient-counting

Detail moved out of [`../status/291-totient-counting.md`](../status/291-totient-counting.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `Nat.countRange_succ_of_true : ∀ f k, Eq Bool (f k) true → Eq Nat
  (countRange f (succ k)) (succ (countRange f k))` — the single-witness
  promotion step `totient_eq_zero`'s own proof already used, extracted as a
  reusable named theorem.
- `Nat.countRange_le_of_le : ∀ f m n, Le m n → Le (countRange f m)
  (countRange f n)` — cardinality monotonicity in the **range bound**
  (distinct from the pre-existing `countRange_le_of_subset`, which is
  monotone in the **predicate**). Via `le_dest`(`m + k = n`) +
  `countRange_split` + `le_add_right`, then transport.
- `Nat.countRange_ge_two_of_two_witnesses : ∀ f n i j, Lt i j → Lt j n →
  Eq Bool (f i) true → Eq Bool (f j) true → Le 2 (countRange f n)` —
  composes the two lemmas above: promote each witness's successor to a
  `≥ 1`/`≥ 2` bound via `succ_le_succ`, carry it to `n` by monotonicity.
  `Lt i j` is definitionally `Le (succ i) j`, so it feeds
  `countRange_le_of_le` with no conversion.

All three admitted on first kernel attempt after one test-only fix: `d.refl`
is hardcoded to `Eq.refl Nat`, so a `Bool`-typed witness needs `d.bool_refl`
— caught by the "sort error wearing a `TypeMismatch`'s clothes" tell
(`expected: ExprId(3)`) this file's own Gotchas section names.

**Each new theorem has a concrete-AND-symbolic test** in
`nat_prelude_tests.rs`, registered in the coverage list
(`theorem_names`/`every_nat_declaration_is_checked_and_axiom_free` — was
red before registration, confirming the guard actually fires). The
`count_range_ge_two_of_two_witnesses` test uses the family's own canonical
case: `n=4`, `f := fun k => beq (gcd k 4) 1`, witnesses `i=1` (always
coprime), `j=3` (top index), with `countRange f 4` checked to be EXACTLY
`2` (not vacuously satisfied by a larger true count).

**Did NOT close any of the 8 open mirrors.** The general machinery is now
in place, but closing `totient_eq_one_iff` or `dvd_two_of_totient_le_one`
still needs a small-numeral trichotomy assembly, not more counting
machinery. The exact route (verified to exist, not attempted) is recorded
in `totient_lemmas.rs`'s module doc's "Update" section:

- The concrete witnesses that make this useful: `i = 1` (`gcd 1 n = 1`
  always, via `Nat.coprime_one_left_iff` — **no `gcd_comm` bridge needed**,
  contrary to the earlier triage's guess, since `totient`'s predicate order
  is `gcd k n` and `coprime_one_left_iff` is already `gcd one n = one`) and
  `j = pred n` (the top index, via `coprime_succ_self`), valid whenever
  `2 < n`.
- `dvd_two_of_totient_le_one` (`0 < a → totient a ≤ 1 → a ∣ 2`): first
  `1 ≤ totient a` from `0 < a` (contrapositive of `totient_eq_zero`), so
  `totient a = 1` (antisymmetry with the hypothesis `≤ 1`). Case-split `a`
  via `finite.rs`'s `trichotomy(d, &p, 2, a)` (already `pub(super)`,
  reusable from a sibling module exactly as `group.rs` already imports
  `le_of_lt`/`pos_implies_succ_pred` from it): `a < 2` + `0 < a` forces
  `a = 1` (`1 ∣ 2` trivial); `a = 2` gives `2 ∣ 2` trivial; `2 < a`
  contradicts `totient a = 1` via `countRange_ge_two_of_two_witnesses` at
  `i=1, j=pred a`.
- `totient_eq_one_iff`'s forward direction closes the same way; its reverse
  direction and the `n ≤ 2` cases are cheap concrete `def_eq` computations
  already noted in the prior triage.

**For the next lane:** the ingredients (`trichotomy`, `lt_or_eq_of_le`,
`le_antisymm`, the three lemmas above) are all present now — this is a
composition task, not a proof-difficulty one. `totient_even` (piece 2) and
the multiplicative formula (piece 3) remain unbuilt and are each their own
slice, sized as before (piece 2 large, piece 3 largest).

**Verification.** `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
165 passed, 0 failed (162 baseline + 3 new, each confirmed to run by name
with a nonzero count, not `0 filtered out`). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean. `python3 scripts/check-test-attribute-integrity.py`: 0 findings.
`python3 scripts/validate-facts.py`: 2034 facts, 0 errors (no fact touched
this session — this lane built infrastructure, not a mirror closure).
`the_build_is_deterministic`'s pin moved from `93 + 531` to `93 + 534`
(3 new theorems), taken from the panic message's own mismatch (627 vs
624), not hand-incremented.

**Commits** (not pushed): `edc6e80a7` (the three theorems + tests + pin),
`10930c319` (module doc update recording the exact route left for the next
lane).
