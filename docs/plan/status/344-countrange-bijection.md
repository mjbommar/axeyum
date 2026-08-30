# Lane: countrange-bijection — the `countRange` permutation primitive is landed and certified

<!-- plan-section: lane-status -->

**DONE (`countrange-bijection`, 2026-08-30).** Built and kernel-checked the
primitive `docs/plan/status/320-totient-bijection.md` named as the one
genuinely missing piece under `Nat.totient_mul_of_coprime`. Three new
theorems, no new `Definition`, all axiom-free, `nat_prelude::` **185 passed,
0 failed** (183 baseline + 2 new tests).

## The primitive

```text
Nat.countRange_permute :
  ∀ (f : Nat → Bool) (σ : Nat → Nat) (n : Nat),
    Nat.InjectiveOn σ n → Nat.MapsInto σ n →
    Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)
```

**Why this statement.** It is the exact `countRange` mirror of
`Int.prodRange_permute` — same hypotheses, same argument order — so the two
read against each other. It is also precisely what the CRT argument needs and
no more: for coprime `m, n` the map `g x := (x mod m) * n + (x mod n)` is an
injective self-map of `[0, m*n)`, and the coprimality predicate satisfies
`P x = Q (g x)` for **every** `x`, not merely `x < m*n` (checked numerically
for all `x < 60` at every `1 ≤ m,n ≤ 9`). So the consumer gets
`countRange Q (m*n) = countRange (Q ∘ g) (m*n)` from this theorem and closes
the last step with the *unconditional* `Nat.countRange_congr` that already
existed. No `P`/`Q` pair and no bounded pointwise agreement are needed in the
statement, so neither is in it.

Supporting, both also new and both reusable:

- **`Nat.countRange_congr_lt`** — `(∀ i, Lt i n → f i = g i) → countRange f n
  = countRange g n`. The BOUNDED pointwise congruence. `countRange_congr`
  (`totient.rs`) is unconditional and its own doc comment says to add this
  form when a proof needs it; this is that proof.
- **`Nat.countRange_point_change`** — `Lt i0 n → (agree below i0) →
  (agree above i0) → countRange a n + sel (b i0) = countRange b n + sel (a i0)`.
  Two predicates agreeing on `[0,n)` except possibly at one index have counts
  differing exactly as their two values there do. Stated additively (`Nat.sub`
  is truncated); the two agreement hypotheses are split at `i0` rather than
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

- `python3 scripts/tests/check-countrange-bijection-numerics.py` — 19 checks,
  each with a negative control that must genuinely fail. Run BEFORE any Rust.
  It **re-derives rather than inherits** the number `316`/`320` warn about: the
  totient product identity fails at **26 of 26** non-coprime pairs with
  `1 ≤ m,n ≤ 9`, smallest counterexample `m = n = 2`.
- `count_range_permute_certifies_a_transposition_with_a_non_injective_negative_control`
  — a REAL instance, not a type-check: `σ := Nat.transposition 1 2` on
  `[0,4)` with both hypotheses discharged by `transposition_injective` /
  `transposition_maps_into`. The predicate `2 ≤ x` is true on `{2,3}` and its
  composite on `{1,3}` — same count, DIFFERENT index sets, both checked, so
  the equality cannot pass as a syntactic identity. Both sides are required to
  COMPUTE to `2`. Negative control: the constant-`0` map is `MapsInto` and not
  injective, and there the counts are 2 against 0 (`!def_eq`).
- `the_count_range_permutation_family_applies_at_free_variables` — all three
  laws at genuinely free `f`, `σ`, `n`, `i0` via `LocalContext`/`infer_in`,
  each inferred type checked against an independently written statement.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **185 passed, 0
  failed**. `clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
  `rustfmt --edition 2024 --check` clean on every touched file.

Two defects this found, neither of which the kernel could:

1. **A transposed `symm` in `add_swap_right`.** `add_assoc x s u` proves
   `(x+s)+u = x+(s+u)`, so reversing it is `symm(end, mid, h)`, not
   `symm(mid, end, h)`. Bisected by toggling the three `declare_*` calls one
   at a time against a single fast test — never by reading the failure list.
2. **The binder order was `f, n, σ`, not `f, σ, n`.** The induction must bind
   `n` (its target) outside `σ` (generalized in the motive), so the admitted
   order disagreed with every doc comment. Both orders type-check; they are
   just different theorems to apply. Found by the free-variable test, not by
   the kernel. Fixed by re-abstracting — binders go in by free variable, so
   their order is free and no proof changed.

## What remains for `Nat.totient_mul_of_coprime`

Two pieces, both independent of each other and of anything above.

**(A) The CRT self-map's two hypotheses.** With `g x := add (mul (mod x m) n)
(mod x n)` on `[0, mul m n)`:
- `MapsInto g (mul m n)` — needs only `mod x m < m` and `mod x n < n`
  (`Nat.mod_lt`, `0 < m`, `0 < n`), no coprimality.
- `InjectiveOn g (mul m n)` — **this is where `Coprime m n` enters and the
  only place it does.** `Nat.crt_unique` (`nat_prelude/crt.rs`, Nat-native —
  NOT `int_prelude/crt.rs`, which is what three prior triages checked). No
  Bézout witness is needed: `Nat.injective_on_imp_surjective_on` supplies
  surjectivity once injectivity and `MapsInto` are in hand.

Numerically confirmed both ways in the script above: the map is injective on
`[0,mn)` at every coprime pair `1 ≤ m,n ≤ 9`, and at **no** non-coprime pair.

**(B) A product/Fubini counting step**, coprimality-INDEPENDENT — and keeping
that straight is the whole lesson of `301`'s false claim. Suggested statement,
hypothesis-driven so it names no `Bool` combinator and the consumer supplies
whatever conjunction it likes:

```text
Nat.countRange_product :
  ∀ (P R S : Nat → Bool) (n m : Nat),
    Lt 0 n →
    (∀ a b, Lt b n → Eq Bool (R a) true  → Eq Bool (P (add (mul n a) b)) (S b)) →
    (∀ a b, Lt b n → Eq Bool (R a) false → Eq Bool (P (add (mul n a) b)) false) →
    Eq Nat (countRange P (mul n m)) (mul (countRange S n) (countRange R m))
```

Induction on `m`. `mul n (succ m) ≡ add (mul n m) n` is defeq (`Nat.mul`
recurses right), so `countRange_split` peels one block of width `n` with no
`Nat.sub` anywhere; the block's own count is `countRange S n` or `0` by
`bool_true_or_false` on `R m` plus `countRange_congr_lt`. Every ingredient
exists: `countRange_split`, `countRange_congr_lt` (new, above),
`Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right`, `Nat.mod_lt`,
`Nat.mul_add`, `Nat.zero_add`, `ops::bool_true_or_false`,
`finite::select_nat_true`/`select_nat_false`. The one genuinely new sub-piece
is a `countRange f n = 0` when `f` is `false` below `n` — a short arrow-motive
induction, the same shape as `countRange_congr_lt`.

Verified numerically at every `1 ≤ n ≤ 7`, `m ≤ 7` and every pair of
predicates (check 6 in the script).

**Assembly, once (A) and (B) exist.** `totient (mul m n)` is
`countRange (fun x => beq (gcd x (mul m n)) 1) (mul m n)`. Rewrite the
predicate pointwise — for ALL `x`, no bound needed — to
`beq (gcd (mod x m) m) 1 ∧ beq (gcd (mod x n) n) 1` using
`Nat.gcd_mod_left_eq_gcd` and `Nat.coprime_mul_iff` (both landed by lane
`320`), reindex along `g` with `Nat.countRange_permute`, then factor with
`Nat.countRange_product`. The two `ml430` totient mirrors need the full
non-coprime formula on top of that, which `316` sizes as a separate
prime-power-factorization framework this kernel does not have; nothing here
changes that sizing.

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/count_range_permute.rs` — new.
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` — `mod`/`use`, three
  `NameId` fields and their `name_str` constructors, three dispatch calls
  placed immediately after `declare_restrict_maps_into`.
- `crates/axeyum-lean-kernel/src/nat_prelude/finite.rs` — five private helpers
  (`po_inner`, `point_override`, `override_eq_lt`/`_gt`/`_at`) widened to
  `pub(super)`. Visibility only; re-deriving them beside the originals would
  leave two proofs of one fact.
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` — two
  tests, three names added to `theorem_names`. No pin reintroduced.
- `scripts/tests/check-countrange-bijection-numerics.py` — new.
