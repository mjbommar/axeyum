# Lane: prime-char-mirrors — the `Mathlib.Data.Nat.Prime.Defs` characterizations

<!-- plan-section: lane-status -->

**DONE (`prime-char-mirrors`, 2026-08-30).** All 15 dispatchable
`ml430-nat-prime-*` facts NOT assigned to the sibling `prime-dvd-mirrors`
lane (which took the divisibility cluster: `prime_dvd_mul`,
`prime_dvd_or_dvd`, `prime_dvd_iff_eq`, `prime_coprime_iff_not_dvd`,
`prime_coprime_pow_of_not_dvd`) are now **proved**, in a new file
`nat_prelude/prime_char.rs`. Three commits (`d2063aec5`, `712b584cf`,
`a895b9b4c`).

```text
Nat.prime_one_le                      Prime p -> 1 <= p
Nat.prime_pos                         Prime p -> 0 < p
Nat.prime_one_lt                      Prime p -> 1 < p
Nat.prime_ne_zero                     Prime p -> p != 0
Nat.prime_ne_one                      Prime p -> p != 1
Nat.prime_not_dvd_one                 Prime p -> ~(p | 1)
Nat.prime_eq_one_or_self_of_dvd       Prime p -> forall m, m|p -> m=1 \/ m=p
Nat.prime_eq_two_or_odd               Prime p -> p=2 \/ Odd p
Nat.prime_eq_two_or_odd_mod           Prime p -> p=2 \/ p%2=1
Nat.prime_mod_two_eq_one_iff_ne_two   Prime p -> (p%2=1 <-> p!=2)
Nat.prime_not_prime_pow_two_le        2<=n -> ~Prime(x^n)
Nat.prime_not_prime_pow_ne_one        n!=1 -> ~Prime(x^n)
Nat.prime_eq_one_of_pow               Prime(x^n) -> n=1
Nat.prime_not_coprime_iff_dvd         ~Coprime m n <-> exists p, Prime p /\ p|m /\ p|n
Nat.prime_mul_eq_prime_sq_iff         Prime p -> x!=1 -> y!=1 -> (x*y=p^2 <-> x=p /\ y=p)
```

`nat_prelude::` **202 passed, 0 failed** (the documented 202 baseline,
grown from 909 filtered-in tests as the 15 new theorem names were added
to `theorem_names` along the way — every intermediate commit was
re-verified at 202 after each addition). `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` and
`cargo fmt --all --check` both clean throughout. `validate-facts.py`:
**2265 facts, 0 errors** after the final commit, via
`check-fact-depends-derived.py --fix` each time.

## Mirror-flip determination

Every `Nat.Prime p` hypothesis is spelled with this prelude's own inline
primality predicate, `2 ≤ p ∧ ∀ c, c ∣ p → c = 1 ∨ c = p`
(`primes.rs`'s `PrimeCond` convention) — this prelude has no `Prime`
predicate at all. That substitution is honest here specifically because
**every one of these 15 facts is itself a characterization of what
primality IS or entails**, not a theorem about some other structure
Mathlib happened to build `Nat.Prime` from. This is the same substitution
already established by prior lanes for `prime_even_iff`,
`prime_odd_of_ne_two`, `prime_dvd_of_dvd_pow`, `prime_not_dvd_mul`,
`prime_pred_pos`, `five_le_of_ne_two_of_ne_three` — all already-proved
facts in this ledger that flip Mathlib's `Nat.Prime` the same way. Every
statement was compared against the landed lemma's RENDERED TYPE
(`nat_theorem_inventory`), never a doc comment, before being trusted.

No target in this batch routes through `Nat.minFac` (the structurally
blocked algorithm), so nothing here hit that wall.

## What each closed fact needed (for the next lane reading this)

- **Six trivial numeric bounds** (`one_le`/`pos`/`one_lt`/`ne_zero`/
  `ne_one`/`not_dvd_one`) are direct consequences of the `2 ≤ p` lower
  bound via the standing `Lt a b` defeq `Le (succ a) b` trick —
  `prime_one_lt`'s proof term IS the lower-bound projection, literally no
  computation.
- **`prime_eq_one_or_self_of_dvd`** is exactly `prime_condition`'s
  divisor clause read out with `and_right` — no proof content at all.
- **The three parity facts** compose the already-proved
  `prime_even_iff`/`prime_odd_of_ne_two` (`primes.rs`) with
  `even_or_odd_exists`/`odd_iff_mod_two_eq_one` (`parity.rs`).
- **The three pow facts** (`not_prime_pow` ×2, `eq_one_of_pow`) share one
  new helper, `prime_pow_ge2_contradiction`: `x` divides `x^n` (witness
  `x^(n-1)`), so the divisor clause forces `x=1` (collapses `x^n` to `1`
  via `one_pow`, contradicts the `2 ≤ x^n` lower bound) or `x=x^n`
  (cancels the shared factor `x` via `mul_left_cancel_of_pos` to force
  `x^(n-2)=1`, hence `x∣1`, refuted by `not_dvd_one_of_two_le`). All three
  theorems are literally the same 3-way case split on `n` (`0`, `1`,
  `succ(succ _)`) read three different ways.
- **`prime_not_coprime_iff_dvd`** needed a genuinely new piece: this
  prelude has no exported "`2` is prime" constant, so a private
  `prime_two` (built from the existing `ops::two_divisor_dichotomy`, not
  re-derived arithmetic) had to be built locally, plus the same
  `lt_or_ge`-twice trichotomy on `gcd m n` the already-proved
  `coprime_of_forall_prime_dvd` uses.
- **`prime_mul_eq_prime_sq_iff`** was the hardest — a real
  structure-of-divisors argument. New private helper
  `prime_sq_factor_case(p, a, b, prime_hyp, ne_b, heq: a*b=p*p, dvd_p_a)`:
  the divisor witness `k` (`a = p*k`) substitutes into `heq` to give
  `k*b = p` (`mul_assoc` + `mul_left_cancel_of_pos`), and `k`'s own
  primality clause forces `k=1` (both factors equal `p`) or `k=p` (forces
  the other factor to `1`, contradicting the caller's `≠1` hypothesis).
  `euclid_lemma`'s two branches both route through this one helper — the
  `p∣y` branch swaps `x`/`y` via `mul_comm` and swaps the resulting `And`
  back, so no arithmetic is duplicated.

## A live gotcha this lane hit and fixed

`d.trans(a, b, c, h1, d.symm(...))` — a nested `d.` call inside another
`d.` call's argument list — is a `E0499` "cannot borrow `*d` as mutable
more than once" compile error, exactly the trap `factorization.rs`'s
module doc already warns about (hoist every sub-expression into its own
`let` first). Caught by `cargo check` on the first attempt at
`prime_mul_eq_prime_sq_iff`; fixed by hoisting the `d.symm(...)` call
into its own `let` binding. Left as a reminder in this file because the
existing warning is easy to read as "applies to deeply nested proof
scripts" when it just as easily bites a single one-line fix.

## Not attempted / not in scope

- The five `prime_dvd_*`/`prime_coprime_*` facts are the sibling
  `prime-dvd-mirrors` lane's targets — not touched.
- `F:nat-totient-*` facts that appeared in the same nursery draw were
  explicitly out of scope per the task brief (only `ml430-nat-prime-*`
  rows were this lane's).
- Nothing in this family was held out (`fermat-numbers` and
  `natural-nth-selector`, this draw's held-out additions, share no
  target with this family).

## Working files

- New: `crates/axeyum-lean-kernel/src/nat_prelude/prime_char.rs`
- Touched (field/name-string additions and one `theorem_names` addition
  per commit): `crates/axeyum-lean-kernel/src/nat_prelude.rs`,
  `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs`
- 15 fact files under `artifacts/facts/F-ml430-nat-prime-*.json` flipped
  `open` → `proved` with kernel-term + axiom-footprint evidence pairs.
