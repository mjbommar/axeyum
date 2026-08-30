# Notes: 379-totient-gcd-mul

Detail moved out of [`../status/379-totient-gcd-mul.md`](../status/379-totient-gcd-mul.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Largest of the three — held.** This file is ~1,150 lines against
  `totient_dvd_chain.rs`'s ~1,840 for BOTH of the other two mirrors combined,
  but the single hardest piece here (the final commutative-monoid assembly)
  is genuinely more intricate than either of theirs.
- **Strong induction on `gcd(a,b)`, base case multiplicativity — held
  exactly.** Generalized as `Nat.totient_gcd_mul_aux : ∀ d a b, gcd a b = d →
  …` by `WellFounded.fix` on `Nat.lt`, mirroring `totient_dvd_chain.rs`'s
  skeleton (case `d=0`: both sides reduce to `0` unconditionally; case `d=1`:
  exactly `Nat.totient_mul_of_coprime` plus `mul_one`/`one_mul`, since
  `totient one` reduces to `one` by pure computation; case `d≥2`: peel a
  prime).
- **Four-leaf case split — held, but Euclid's lemma is NOT load-bearing on
  the route actually taken.** ADR-0668's sketch decides `q | gcd(a₁,b₁)` and
  `q | a₁·b₁` as two SEPARATE questions and needs Euclid's lemma to reconcile
  them into a four-case `ε` truth table (`p|a₁,p|b₁` ⟺ `p|gcd`, `p|a₁ ∨ p|b₁`
  ⟺ `p|a₁·b₁`, and the second equivalence's forward direction IS Euclid).
  This proof instead decides `Nat.coprime_or_dvd_of_prime` on `a₁` and on
  `b₁` INDEPENDENTLY (the two outer/inner branches of a nested `or_cases`),
  and DERIVES the status of `gcd(a₁,b₁)` and `a₁·b₁` from those two decisions
  via `Nat.dvd_gcd` / `Nat.coprime_of_dvd_right` / `Nat.coprime_mul_of_coprime`
  / `Nat.dvd_mul_{left,right}_of_dvd` — never asking the question Euclid's
  lemma would answer, so it is never needed on this route. Both routes are
  correct; this one needs one fewer number-theoretic input.

## The one thing I got wrong on the first attempt

The induction hypothesis `ih` (from `WellFounded.fix`'s own step function) is
stated in terms of the fix's own bound variable `x`, not the locally-bound
`kx := succ pv` that the case split introduces. `derive_cofactor_lt` (copied
from `totient_dvd_chain.rs`) returns `Lt g1 kx`, and applying `ih` directly at
that proof is a `TypeMismatch` — `ih` expects `Lt g1 x`. The fix is one more
`transport` along the outer `heq : Eq x kx`, exactly mirroring
`totient_dvd_chain.rs`'s own `lt_proof_kx` → `lt_proof_x` step (which I had
read and still omitted on the first pass). The kernel caught it immediately
as a `TypeMismatch` on `nat_prelude::nat_prelude_tests::the_build_is_
deterministic`, rendered both sides with a temporary `render_lean` debug
print, and the fix was obvious once rendered:
`Le (succ (gcd _)) fvar4` (expected, the outer `x`) vs
`Le (succ (gcd _)) (succ fvar35)` (got, `kx`).

## Numeric checks (re-executable, re-run rather than inherited)

```sh
python3 scripts/tests/check-totient-prime-power-numerics.py   # 37 checks, 0 failed
```

Checks `8`, `8A`, `8N`, `8E`, `8EN`, `8G`, `8R` are this target's. `8N` shows
the identity is STRICTLY STRONGER than multiplicativity (53 non-coprime pairs
with `1 ≤ a,b ≤ 12`); `8EN` shows ADR-0668's own `ε`-identity sketch route
needs Euclid (fails at 450 composite triples) — this file's actual route
sidesteps that identity entirely, so `8EN` bounds a DIFFERENT route's
obstruction, not this proof's.

A new negative control in the kernel test itself
(`totient_gcd_mul_totient_mul_applies_at_free_variables_and_a_non_coprime_
instance`) checks the statement at free `(a,b)`, that plain multiplicativity
is NOT `def_eq` to this identity, the coprime collapse at `(3,4)`, and the
non-coprime case `(6,4)` where multiplicativity alone is FALSE
(`totient 24 = 8`, not `totient 6 * totient 4 = 4`) but the full identity
holds (`1*8 = 2*2*2`).

## What's in the ledger now

`F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`: `open` → `proved`,
`kernel_theorem: Nat.totient_gcd_mul_totient_mul`, `axiom_footprint: []`,
`proof_route: kernel-lean`, `depends_on: [F:nat-totient-mul-of-coprime,
F:nat-totient-mul-of-dvd]`. Re-checked partition before touching:
`development` (`nursery-v2-extension.json`), not held-out.

**All three `ml430` totient mirrors ADR-0668 named are now closed**:
`F:ml430-nat-totient-dvd-of-dvd-9622e44a`,
`F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` (both closed earlier
the same day by the `totient-dvd-chain` lane), and this one.
