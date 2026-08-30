# Lane: totient-prime-power — `Nat.totient_prime_pow`, and the three mirrors reassessed

<!-- plan-section: lane-status -->

**DONE (`totient-prime-power`, 2026-08-30).** Six theorems landed in a new
file `nat_prelude/totient_prime_pow.rs`, **all six admitted by the kernel on
the first attempt**, all axiom-free, no new `Definition`. `nat_prelude::`
**201 passed, 0 failed** (196 baseline + 4 new tests + the coverage assertion,
which fired correctly before the names were registered). `cargo fmt --all
--check` clean; `clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
clean; `validate-facts.py` **2225 facts, 0 errors**;
`scripts/gen-adr-index.py` exit 0.

```text
Nat.countRange_const_true          ∀ n, countRange (fun _ => true) n = n
Nat.coprime_mul_iff_of_dvd         e ∣ m → (gcd k (m*e) = 1 ↔ gcd k m = 1)
Nat.totient_mul_of_dvd             e ∣ m → φ(m*e) = φ(m)*e
Nat.totient_pow_succ_of_prime      Prime q → φ(q^(j+1)) = (q-1)*q^j
Nat.totient_prime_pow              Prime q → φ(q^(j+1)) = q^(j+1) - q^j
Nat.totient_dvd_totient_mul_prime  Prime q → φ(x) ∣ φ(x*q)
```

Three hand-curated ledger facts: `F:nat-totient-mul-of-dvd`,
`F:nat-totient-prime-pow`, `F:nat-totient-dvd-totient-mul-prime`.

## The assessment the task asked for first

**All three remaining `ml430` mirrors are reachable WITHOUT multiset
uniqueness.** The Euler-product route needs it; a prime-peeling induction does
not, and that is the finding — recorded as
[ADR-0668](../../research/09-decisions/adr-0668-the-totient-mirrors-do-not-need-multiset-uniqueness.md)
with the full argument and the simulated inductions.

This **corrects** `349`'s sizing. That lane wrote that both mirrors "need the
non-coprime formula, which needs a totient value at prime powers plus a
product over a factorization" — right about the *Euler-product route*, and it
reads as a statement about the *targets*. It is the standing failure mode this
repository has now hit three times: a handoff reports accurately on its own
route, and the route-local blocker gets promoted into a claim about the goal.

Why uniqueness drops out, in one sentence: each target is **preserved along a
chain of prime steps**, the chain is built from *some* factorisation of the
cofactor, and nothing ever compares two factorisations — so nothing needs them
to agree. Uniqueness is required only to *evaluate* a closed-form product,
which none of these arguments does.

The only number-theoretic inputs are `Nat.exists_prime_dvd` (every `n > 1` has
a prime divisor — far weaker than unique factorisation), `Nat.euclid_lemma`,
`Nat.gcd_mul_right`, and the prime step. **All four now exist.**

## Numeric checks, as re-executable commands

```sh
python3 scripts/tests/check-totient-prime-power-numerics.py   # 37 checks, 0 failed
python3 scripts/tests/check-totient-mul-coprime-numerics.py   # exit 0
python3 scripts/tests/check-countrange-bijection-numerics.py  # exit 0
```

The two prior scripts were **re-run, not inherited** — a traced plan in this
exact area asserted an identity was coprimality-independent and "verified
numerically", and it is false at 26 of 26 non-coprime pairs.

Every positive check is exhaustive over its stated range and every negative
control is asserted to *genuinely* fail:

| claim | check | control |
| --- | --- | --- |
| the gcd bridge needs `e ∣ m` | `3` | `3N` — fails at 165 non-dividing pairs |
| `φ(m·e) = φ(m)·e` for `e ∣ m` | `4` | `4N` — fails at 493 pairs, smallest `(1,2)` |
| `φ(p^k) = p^k − p^(k−1)` | `5` | `5N` — fails at 42 composite `(c,k)`, smallest `c=4,k=1` |
| the prime step's ε law | `6` | `6N` — fails at 488 composite multipliers |
| Target 1 | `7`, `7R` | `7N` — hypothesis load-bearing |
| the ε identity Target 2 reduces to | `8E` | `8EN` — fails at 450 composite triples |
| Target 2 | `8`, `8R` | `8N` — strictly stronger than multiplicativity |
| Target 3 | `9`, `9E`, `9T` | `9N` — hypothesis load-bearing |
| the landed prime step | `11` | `11N` — transposed direction, fails at 142 pairs |

Check `10` speaks directly to the ADR's claim: it re-runs Target 1's peeling
induction with a **greatest-first** rather than least-first choice of prime at
each step and requires the same verdict. If uniqueness were load-bearing the
two orders could disagree. They do not.

## The one thing I nearly got wrong, and it is a control

**A composite control on `totient_dvd_totient_mul_prime` would be VACUOUS.**
The obvious move — copy the composite control that discriminates
`totient_prime_pow` — produces a check that cannot fail, because `φ(x) ∣ φ(x·q)`
is Target 1 specialised (`x` always divides `x·q`) and is therefore **true at
every composite `q` too**, failing at zero of them. Primality is a requirement
of the proof *route*, not of the proposition.

Check `11V` measures that rather than assuming it, and the usable control is
the **transposed** divisibility (`11N`, smallest failure `x = 1, q = 3`, where
`φ(3) = 2` does not divide `φ(1) = 1`). This is the "negative controls fail
two ways" trap arriving through the door marked *reuse*, and it is the third
time this area has produced one.

## What the counting law actually is

`Nat.totient_mul_of_dvd` is the whole content of the file. It carries **no
primality, no positivity and no factorisation** — the hypothesis is `e ∣ m`
and nothing more — and it needs no induction of its own:

1. `Nat.countRange_congr` across the gcd bridge, which is the **only** place
   the hypothesis is spent. Forward is `Nat.coprime_mul_iff`'s `mp` (already
   unconditional); backward is its `mpr` with `Nat.coprime_of_dvd_right`
   supplying `gcd k e = 1`.
2. `Nat.countRange_product` at block width `m` and block count `e`. Its
   per-block hypothesis is `Nat.div_mod_block` composed with
   `Nat.gcd_mod_left_eq_gcd`; the `R a = false` row is vacuous because `R` is
   the constant `true`. **`countRange_product` already did the induction.**
3. `Nat.countRange_const_true` collapses the block-count factor — the one
   genuinely new small lemma, a three-line induction that did not exist.

`countRange S m` is `totient m` *on the nose*, because `S` is built by exactly
`totient.rs`'s own predicate recipe, so nothing bridges the two.

The prime power then follows by induction on the exponent, with
`Dvd q (q^(j+1))` supplied by `Nat.dvd_mul_left` and **no arithmetic lemma at
all** — `pow` recurses on its exponent, so `pow q (succ j)` is *definitionally*
`mul (pow q j) q`. Primality enters in exactly one place, the base case,
through `Nat.totient_prime`.

## Per-target status

- **`F:ml430-nat-totient-dvd-of-dvd-9622e44a` — OPEN, unblocked.** Needs only
  the well-founded induction chaining `Nat.totient_dvd_totient_mul_prime`
  along a factorisation of `b/a`, terminating because each step strictly
  reduces the cofactor. No new number theory.
- **`F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` — OPEN, unblocked.**
  The same chain, with the multiplier tracked: `ε = 1` exactly when `q = 2` and
  the current value is odd (check `9E`), and one such step makes the value
  even (check `9T`), so the chain has length 0 or 1.
- **`F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7` — OPEN, unblocked but
  the largest of the three.** Strong induction on `gcd(a,b)`, base case the
  already-landed `totient_mul_of_coprime`. Peeling one prime reduces the whole
  identity to the four-leaf ε truth table (check `8E`); Euclid's lemma is the
  only place primality is used, and check `8EN` shows it is load-bearing —
  the identity fails at 450 composite triples.

All three re-checked as `partition: development` before being touched (3 rows
found against a positive control). **None is held-out.**

## Two notes for whoever takes the next rung

- **A single-test filter is not a gate for a prelude change.** One bad
  declaration poisons the shared prelude build, so the failure *count* tells
  you nothing; bisect by toggling `declare_*` calls one at a time.
- `nat_theorem_inventory` silently keeps only ONE of several name arguments —
  the **LAST** one, where `theorem_dependency_inventory` keeps the first.
  Pass one name per invocation. All three facts' checkers do.

## Landed changes

| what | where |
| --- | --- |
| six theorems | `crates/axeyum-lean-kernel/src/nat_prelude/totient_prime_pow.rs` |
| names, docs, dispatch | `crates/axeyum-lean-kernel/src/nat_prelude.rs` |
| four tests + coverage list | `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` |
| 37 numeric checks | `scripts/tests/check-totient-prime-power-numerics.py` |
| three ledger facts | `artifacts/facts/F-nat-totient-{mul-of-dvd,prime-pow,dvd-totient-mul-prime}.json` |
| the reachability decision | `docs/research/09-decisions/adr-0668-…md` |
