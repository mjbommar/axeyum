# Notes: 313-totient-mult-finish

Detail moved out of [`../status/313-totient-mult-finish.md`](../status/313-totient-mult-finish.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`F:ml430-nat-totient-coprime-totient-iff-3932cf83`** — `proved`,
`kernel-lean`, `axiom_footprint: []`. `Nat.totient_coprime_totient_iff`
(`nat_prelude/totient_lemmas.rs::declare_totient_coprime_totient_iff`) was
built exactly as `306`'s handoff traced it, with no surprises: `mpr` is
unconditional composition via `totient_eq_one_iff` +
`coprime_one_left_iff`/`coprime_one_right_iff`; `mp`'s hard case (`2<m,
2<n`) refutes two evens sharing `gcd = 1` — each is divisible by `2`
(`succ_mul`/`one_mul` turn the `Even` witness `k+k` into `mul two k`), then
`dvd_gcd` + `eq_one_of_dvd_one` force `Eq two one`, refuted by transporting
`le_refl two` along it and peeling one `succ` to `not_succ_le_zero` — the
same ending `totient_le_one_contradiction_above_two`/`n_ne_one_from_lt_two`
already use. The `m=0`/`n=0` sub-cases route through `gcd_zero_left`
directly (`m=0`) or `gcd_comm`+`gcd_zero_left` (`n=0`, since this prelude
has no named `gcd_zero_right`). Type-checked on the first kernel-verification
attempt after fixing five E0499 double-mutable-borrow compile errors
(`d.eq(...)` computed inline as a second argument to a call already
borrowing `d` — precompute into a local first). Six new local helpers
(`exists_elim`, `even_dvd_two`, `refute_eq_two_one`,
`close_via_gcd_left_one`/`close_via_gcd_right_one`,
`totient_n_eq_one_from_m_zero`, `totient_m_even_n_zero_contradiction`), all
in `totient_lemmas.rs`, none registered as facts (infrastructure, not
axioms — the empty-footprint evidence bounds them).

Pinned by a concrete-instantiation test at `(m,n)` = `(1,9)` (left disjunct
holds), `(6,2)` (right disjunct holds), `(6,9)` (discriminating: `totient 6
= 2`, `totient 9 = 6`, `gcd 2 6 = 2 != 1`, checked directly by `!def_eq`
before applying the theorem) plus a genuinely free `(m,n)` via
`LocalContext`/`infer_in`.

`depends_on` completed via `scripts/check-fact-depends-derived.py --fix`
(`missing_edges=0` after the fix, 8 edges added). Both evidence
`checker_command`s verified to pass on the real name (count 1) and fail on
a fabricated one (count 0).

## `Nat.coprime_mul_of_coprime` — the first weak piece, landed

**`Nat.coprime_mul_of_coprime : ∀ x m n, Eq (gcd x m) one → Eq (gcd x n)
one → Eq (gcd x (mul m n)) one`** (Mathlib's `Nat.Coprime.mul_right`) is now
declared in `nat_prelude/totient_multiplicative.rs`, axiom-free. `301`'s own
triage flagged this as the coprimality-combine weakest step and sketched two
untried routes; **route (b) (the prime-divisor contrapositive) worked on the
first kernel-verification attempt** and sized SMALLER than the doc's own
estimate — every ingredient it needs was already declared:

- `Nat.euclid_lemma : ∀ p a b, prime p → p ∣ a*b → p ∣ a ∨ p ∣ b`
  (`bezout.rs`).
- `Nat.coprime_of_forall_prime_dvd : ∀ m n, (∀ k, prime_condition k → dvd k
  m → dvd k n → dvd k one) → gcd m n = one` (`primes.rs`) — this is the
  actual load-bearing piece, and the doc's triage did not name it; it turns
  the whole proof into supplying one hypothesis function rather than doing
  gcd-antisymmetry case analysis by hand.

The proof: apply `coprime_of_forall_prime_dvd` at `(x, mul m n)`, supplying
`hyp := fun k (prime_k) (hkx : dvd k x) (hkmn : dvd k (mul m n)) => …`. Inside,
`euclid_lemma(k, m, n, prime_k, hkmn)` splits into `dvd k m ∨ dvd k n`; each
branch combines with `hkx` via `dvd_gcd` into `dvd k (gcd x m)` / `dvd k (gcd
x n)`, transported along the corresponding coprimality hypothesis (the
theorem's own `h_xm`/`h_xn`) to `dvd k one`. `prime_condition` is a local
copy of `primes.rs`'s private helper (`2 ≤ x ∧ ∀ c, c∣x → c=1 ∨ c=x`), per
this task's own local-copies-per-file convention (`primes.rs` is not this
task's file). **No Bézout-coefficient algebra (route (a)) was needed at
all** — the balanced-Bézout multiplication case analysis `301` worried about
never came up.

Pinned by a concrete instance (`x=5, m=2, n=3`: `gcd 5 2 = gcd 5 3 = 1` by
reduction, concluding `gcd 5 6 = 1`, checked by reduction too) plus a
genuinely free `(x,m,n)` with free hypotheses pushed into an explicit
`LocalContext`. Not attached to a fact — like `gcd_comm` before it, an
unregistered nat-prelude helper theorem.

## What's left: `Nat.count_range_row_major`, then the assembly

The **second** weak piece from `301` — `Nat.count_range_row_major : ∀ P Q m
n, countRange (fun x => Bool.and (P (mod x m)) (Q (mod x n))) (mul m n) =
mul (countRange P m) (countRange Q n)`, the totient-independent
double-counting identity — was **not attempted this session** (budget, per
this task's own "don't force the formula" instruction). `301`'s proof
sketch is unchanged and still the best plan: induct on the ROW COUNT (not
on `m` used as a modulus directly), following `rectangle.rs`'s existing
row/shift machinery (`row_fn`/`row_sum`/`shifted`, already `pub(super)` and
reused cross-file per that module's own doc — `totient.rs` already imports
`shifted` for an unrelated purpose, so the precedent is direct).

Once `count_range_row_major` exists, `301`'s Steps 1 (mod-gcd invariance,
small, `gcd_succ`+`gcd_comm`, both now available), 3 (pointwise predicate
iff, composes `coprime_mul_of_coprime`'s shrink-half siblings
`coprime_mul_left_right`/`coprime_mul_right_right` plus Step 1), and 5
(assembly via `countRange_congr`) compose into
`Nat.totient_mul_of_coprime : ∀ m n, Coprime m n → totient (mul m n) = mul
(totient m) (totient n)`, which is what all three remaining facts need:

```
F:ml430-nat-totient-dvd-of-dvd-9622e44a
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
```

None of these three were attempted; each needs the full multiplicative
formula (confirmed against their `formal.statement` fields), and
`totient_gcd_mul_totient_mul` additionally needs the formula applied to
`m`/`n`'s shared-prime-power structure (further work beyond the coprime
case). `scripts/brief-step0.py` confirms all four targets were ABSENT
before this session (one snapshot-STALE warning on each run, correctly
flagged as provisional — refreshed by direct `cargo run --example
nat_theorem_inventory` checks instead of trusting the snapshot).

## Files

- `crates/axeyum-lean-kernel/src/nat_prelude/totient_lemmas.rs` —
  `declare_totient_coprime_totient_iff` and its six local helpers.
- `crates/axeyum-lean-kernel/src/nat_prelude/totient_multiplicative.rs` —
  `declare_coprime_mul_of_coprime` and its local `prime_condition` copy.
- `crates/axeyum-lean-kernel/src/nat_prelude.rs` — two new `NameId` fields
  (`totient_coprime_totient_iff`, `coprime_mul_of_coprime`) and their
  dispatch (both placed immediately after their last dependency).
- `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` — two new
  tests, both added to `theorem_names` (environment-derived coverage
  assertion), determinism pin moved `93+571 -> 93+572 -> 93+573` across the
  two landings (each taken from the panic's own mismatch).
- `artifacts/facts/F-ml430-nat-totient-coprime-totient-iff-3932cf83.json` —
  flipped to `proved`, `depends_on` completed by
  `scripts/check-fact-depends-derived.py --fix`.

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 179 passed, 0
  failed (177 baseline for this dispatch + 2 new tests, each confirmed to
  run by name with a nonzero count).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` and
  `rustfmt --edition 2024 --check` on every touched file: clean.
- `python3 scripts/check-test-attribute-integrity.py`: 0 findings.
- `python3 scripts/validate-facts.py`: 2154 facts, 0 errors.
- `python3 scripts/check-mirror-statement-fidelity.py`: PASS
  (`hash_verified=402`, `violations=0`).

## Commits (not pushed)

- `caae7bab3` — wip: `Nat.totient_coprime_totient_iff` built, kernel-check
  pending (landed within the first ten tool calls, per "commit before any
  long check").
- `d9e03b9da` — the working, kernel-verified `Nat.totient_coprime_totient_iff`
  plus its test, coverage entry, and pin.
- `2dcee349e` — the fact flips to `proved`.
- `b71354322` — `Nat.coprime_mul_of_coprime`, verified, test, coverage entry,
  pin. Not attached to a fact (infrastructure).
