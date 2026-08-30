# Notes: 344-countrange-bijection

Detail moved out of [`../status/344-countrange-bijection.md`](../status/344-countrange-bijection.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

  Induction on `m`. `mul n (succ j) ≡ add (mul n j) n` is definitional
  (`Nat.mul` recurses right), so `countRange_split` peels one block of width
  `n` with no `Nat.sub` anywhere.

- **`Nat.div_mod_block`** — `∀ n a b, Lt b n → div (n*a + b) n = a ∧
  mod (n*a + b) n = b`. The bridge `countRange_product`'s consumer needs:
  that lemma's hypotheses live at the index `add (mul n a) b`, and a predicate
  written in `div y n` / `mod y n` reduces there only once these hold. One
  line of content once `Nat.div_mod_unique` is used — the witness
  `divMod n (n*a+b) a b` is `And.intro (Eq.refl _) hb` and costs nothing.
  Filed in `div_mod_lemmas.rs` where it belongs, **not** beside its first
  consumer.

- **`Nat.countRange_congr_lt`** — the BOUNDED pointwise congruence.
  `countRange_congr` (`totient.rs`) is unconditional and its own doc comment
  says to add this form when a proof needs it; this is that proof.

- **`Nat.countRange_point_change`** — `Lt i0 n → (agree below i0) →
  (agree above i0) → countRange a n + sel (b i0) = countRange b n + sel (a i0)`.
  Two predicates agreeing on `[0,n)` except possibly at one index have counts
  differing exactly as their two values there do. Stated additively (`Nat.sub`
  is truncated); the agreement hypotheses are split at `i0` rather than
  written as one `k ≠ i0`, so nothing needs `Not`-elimination.

## What `320` looked for, and where it actually was

`320` searched `permutation.rs`, `cardinality.rs` and `subset_product.rs`,
found "the pieces a proof would COMPOSE from" but no such statement, and sized
this as "likely the largest remaining piece". The search was correct and the
sizing was not, for one reason: **`Int.prodRange_permute` has existed since
Wilson's theorem** (`int_prelude/prod.rs`). Hiding place 1 from `CLAUDE.md` —
general infrastructure filed under its first consumer — compounded by being in
a different PRELUDE and over a different aggregate, so no `Nat`-side name or
shape search reaches it.

So the induction skeleton was copied, not invented: `f` outside the recursion,
motive generalized over `σ`, pigeonhole locating `i0` with `σ i0 = n`, branches
`i0 = n` and `i0 < n`. The `i0 < n` branch reuses `Nat.restrict_injective` and
`Nat.restrict_maps_into` (`finite.rs`) **unchanged** — `finite.rs`'s own
module comment says they were built for exactly this step.

What is not copied is the expensive half. `Int.prodRange_permute` needs
`Int.prodRange_swap` to move a value between slots, itself an
adjacent-transposition induction `wilson.rs` records as taking three drafts.
Counting needs no swap at all, because `countRange` accumulates with
`Nat.add`. `countRange_point_change` replaces the whole apparatus with one
induction and an `add` rearrangement per branch.

## Verification

- `python3 scripts/tests/check-countrange-bijection-numerics.py` — 25 checks,
  each with a negative control that must genuinely fail. Run BEFORE any Rust.
  It **re-derives rather than inherits** the number `316`/`320` warn about: the
  totient product identity fails at **26 of 26** non-coprime pairs with
  `1 ≤ m,n ≤ 9`, smallest counterexample `m = n = 2`.
- `count_range_permute_certifies_a_transposition_with_a_non_injective_negative_control`
  — a REAL instance, not a type-check: `σ := Nat.transposition 1 2` on
  `[0,4)` with both hypotheses discharged by `transposition_injective` /
  `transposition_maps_into`. The predicate `2 ≤ x` is true on `{2,3}` and its
  composite on `{1,3}` — same count, DIFFERENT index sets, both checked, so
  the equality cannot pass as a syntactic identity. Both sides required to
  COMPUTE to `2`. Negative control: the constant-`0` map is `MapsInto` and not
  injective, and there the counts are 2 against 0 (`!def_eq`).
- `count_range_product_computes_at_a_factoring_predicate_with_a_non_factoring_control`
  — a CLOSED instance at `n = 0` (both hypotheses discharged from
  `not_lt_zero`; degenerate but assumption-free, and the case that would be
  unreachable had the lemma carried the `Lt 0 n` it does not); the statement
  at `n = 2, m = 3` with all four counts required to compute; and a
  non-factoring `P` where the sides are 2 against 1.
- `div_mod_block_reads_a_concrete_block_back_and_needs_its_side_condition`
  — a CLOSED instance at `(3, 2, 1)` with a real `Lt 1 3`, both projections
  computing, and a control at `b = n` where the readback is wrong BOTH ways.
- `the_count_range_permutation_family_applies_at_free_variables` — all three
  `countRange` laws at genuinely free `f`, `σ`, `n`, `i0` via
  `LocalContext`/`infer_in`, each inferred type checked against an
  independently written statement.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **187 passed, 0
  failed**. `clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
  `rustfmt --edition 2024 --check` clean on every touched file.

Three defects the tests found that the kernel could not:

1. **A transposed `symm` in `add_swap_right`.** `add_assoc x s u` proves
   `(x+s)+u = x+(s+u)`, so reversing it is `symm(end, mid, h)`, not
   `symm(mid, end, h)`. Bisected by toggling the `declare_*` calls one at a
   time against a single fast test — never by reading the failure list.
2. **The permutation lemma's binder order was `f, n, σ`, not `f, σ, n`.** The
   induction must bind `n` (its target) outside `σ` (generalized in the
   motive), so the admitted order disagreed with every doc comment. Both
   orders type-check; they are just different theorems to apply. Found by the
   free-variable test. Fixed by re-abstracting — binders go in by free
   variable, so their order is free and no proof changed.
3. **`transposition_injective` is `∀ i j, Lt i j → ∀ n, …`, not `∀ i j n,
   Lt i j → …`.** Only the concrete test could catch this; the doc comment in
   `nat_prelude.rs` reads in the other order.

## What remains for `Nat.totient_mul_of_coprime`

One piece plus the assembly. Every ingredient below was checked to exist.

**(A) The CRT self-map's two hypotheses**, with `g x := add (mul (mod x m) n)
(mod x n)` on `[0, mul m n)`. This is `320`'s step (1) and the only place
coprimality enters.

- `MapsInto g (mul m n)` — needs `0 < m`, `0 < n` and nothing else:
  `mod x m < m` and `mod x n < n` (`Nat.mod_lt`), then
  `(x mod m)*n + (x mod n) < ((x mod m)+1)*n ≤ m*n`.
- `InjectiveOn g (mul m n)` — from `g x = g y`, apply
  **`Nat.div_mod_block`** (landed here) twice, with `Nat.mod_lt` supplying
  `x mod n < n`, to get `x mod m = y mod m` and `x mod n = y mod n`. Feed
  those to `Nat.div_mod_same_remainder_mod_eq` for `modEq m x y` and
  `modEq n x y`, then **`Nat.crt_unique`** (`nat_prelude/crt.rs` — the NAT
  one, Nat-native; three prior triages checked only `int_prelude/crt.rs`) for
  `modEq (m*n) x y`, then `Nat.div_mod_remainder_eq_of_mod_eq` plus
  `Nat.mod_eq_self_of_lt` twice to turn that into `x = y` given `x, y < m*n`.

  **No Bézout witness and no CRT existence is needed.** `nat_prelude/crt.rs`
  declines existence over ℕ deliberately and at length — the classical witness
  needs signed coefficients — and the injectivity argument never asks for it.
  `Nat.injective_on_imp_surjective_on` supplies surjectivity for free once
  injectivity and `MapsInto` are in hand, if a later step wants it.

  Numerically confirmed both ways (check 4 of the script): the map is
  injective on `[0,mn)` at every coprime pair `1 ≤ m,n ≤ 9`, and at **no**
  non-coprime pair.

**(B) Assembly.** `totient (mul m n)` is
`countRange (fun x => beq (gcd x (mul m n)) 1) (mul m n)`.

1. Rewrite the predicate pointwise — for ALL `x`, no bound needed, so
   *unconditional* `Nat.countRange_congr` suffices — into
   `R (div (g x) n) ∧ S (mod (g x) n)` where `R a := beq (gcd a m) 1` and
   `S b := beq (gcd b n) 1`, using `Nat.gcd_mod_left_eq_gcd` and
   `Nat.coprime_mul_iff` (both landed by lane `320`) together with
   `Nat.div_mod_block`.
2. Reindex along `g` with **`Nat.countRange_permute`**, discharging its two
   hypotheses from (A).
3. Factor with **`Nat.countRange_product`**, discharging its two per-block
   hypotheses from `Nat.div_mod_block` — `R a` is already pinned by each
   hypothesis, so both reduce.

The two `ml430` totient mirrors (`F:ml430-nat-totient-dvd-of-dvd-9622e44a`,
`F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`) need the full non-coprime
formula on top of that, which `316` sizes as a separate prime-power-
factorization framework this kernel does not have. Nothing here changes that
sizing, and `nat_prelude/factorization.rs` is explicit that uniqueness of
factorization is not reachable without a multiset type.

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/count_range_permute.rs` — new.
  `countRange_congr_lt`, `countRange_point_change`, `countRange_permute`,
  `countRange_product`.
- `crates/axeyum-lean-kernel/src/nat_prelude/div_mod_lemmas.rs` —
  `declare_div_mod_block` appended; `div_mod_reconstructed` widened to
  `pub(super)` rather than copied a third time.
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` — `mod`/`use`, five `NameId`
  fields and their `name_str` constructors, five dispatch calls placed
  immediately after `declare_restrict_maps_into`.
- `crates/axeyum-lean-kernel/src/nat_prelude/finite.rs` — five private helpers
  (`po_inner`, `point_override`, `override_eq_lt`/`_gt`/`_at`) widened to
  `pub(super)`. Visibility only.
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` — four
  tests, five names added to `theorem_names`. No pin reintroduced.
- `scripts/tests/check-countrange-bijection-numerics.py` — new, 25 checks.

No fact file was touched: like `gcd_comm` and `coprime_mul_of_coprime` before
them, these are unregistered nat-prelude helper theorems. The facts they serve
stay `open` until `totient_mul_of_coprime` itself lands.
