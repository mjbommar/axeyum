# 01 — Number theory

Reviewer: an elementary and analytic number theorist
Verdict, 2026-09-04: **impressed, with a visible ceiling**
Last measured: 2026-09-04 at `1856cdb3c`

> "This is a real library. It is also 1830s number theory, and you have built
> it so well that the wall it hits is now unmistakable."

## The persona

Works on primes, congruences, Diophantine equations, and L-functions. Values
theorems with names and a proof you can follow. Deeply unimpressed by
infrastructure claims and completely convinced by Wilson's theorem. Their test
for whether a formalization is serious is quadratic reciprocity: it is the
first result in the subject that cannot be bluffed, it has no short proof, and
every real library has it or is not yet real.

## What the library has today

**Combined the largest area in the ledger: 862 proved ℕ facts and 356 proved
ℤ facts, 1,218 together, against 257 open.**

Named results present, all with empty axiom footprint:

| result | where |
|---|---|
| Wilson's theorem | `Int.wilson`, with `Int.wilsonHalfSplit` |
| Quadratic reciprocity | `Int.legendreSym`, `Int.firstSupplementaryLaw{Residue,NotResidue}`, `Int.secondSupplementaryLaw` |
| Fermat's little theorem | `Int.pow_prime_sub_one_modeq_one` |
| Euler's totient | `Nat.totient` and its computation lemmas |
| Bézout's identity | `Int.bezout_witnesses` |
| Chinese remainder theorem | `crt_exists`, `crt_unique` |
| Euclid's infinitude of primes | `euclid_infinitude` |
| Irrationality of √2 | `Nat.no_rational_sqrt_two` |
| Kummer/Pascal divisibility | "a prime divides the interior binomial coefficients of its own row" |
| gcd and Fibonacci | `Int.gcd_fib` |
| Modular arithmetic | a large `Int.ModEq` family: cancellation, `of_mul_left`, `cancel_left_div_gcd`, negation of modulus |
| Least-number principle | `Nat.lnp_bounded_search`, `Nat.least_divisor_search`, `Nat.lnp_decidable` |

The ℤ carrier is characterized categorically (`Int.Characterization.categorical`,
with `induction`, `injective`, `surjective`, `rec_unique`), which is unusual
and worth more to a foundations reader than to this one.

The 257 open ℕ/ℤ facts are almost all transcribed Mathlib v4.30 propositions
sitting in the ledger as a work queue: `Nat.choose_lt_pow`,
`Int.exists_least_of_bdd`, `Int.add_emod`, and so on. That is a declared
frontier, not a gap in the record.

## Their verdict

Wilson and quadratic reciprocity, constructively, with nothing assumed, is the
point at which they stop treating this as a toy. The reciprocity proof route
through Legendre symbols and both supplementary laws is the real one, not a
special case dressed up. The modular arithmetic underneath is broad enough
that they would believe a new congruence result could be proved here in an
afternoon.

Then they would look for the next shelf and not find it. Everything present is
**elementary** number theory in the technical sense: it lives in ℤ and ℕ with
divisibility and congruence, and never leaves. The subject as practised since
Dedekind lives in rings of integers, ideals, and class groups, and none of
that exists. Analytic number theory needs complex analysis, which needs the
classical apparatus this library does not have either.

So their summary: excellent up to about 1830, and the reason it stops there is
structural rather than a matter of effort.

## What they would say is missing

- **Algebraic number theory, entirely.** No rings of integers, no ideals, no
  unique factorization in a Dedekind domain, no class group, no units theorem.
- **Multiplicative structure.** No Möbius function, no Dirichlet convolution,
  no multiplicativity of the totient proved as a general property, no
  arithmetic functions as a family.
- **Primitive roots and the structure of (ℤ/n)\*.** This is elementary, it is
  reachable, and its absence is the most surprising one given what is present.
- **Analytic anything.** No prime counting, no Chebyshev bounds, no Dirichlet
  series, no L-functions, no zeta.
- **Classical Diophantine results.** No Pell's equation, no sums of two
  squares, no continued fractions, no descent as a reusable method.

## The blocker

Two, of different kinds.

**For algebraic number theory: `Quot.sound`.** ℤ/n as a quotient ring, ideals
as quotients, and every construction downstream of them require proving that
related representatives are equal, which this kernel cannot do. The modular
arithmetic here is done with an explicit `ModEq` relation instead, which works
and does not scale to ideals. See [04-algebra.md](04-algebra.md).

**For analytic number theory: the classical analysis stack.** Complex
analysis, contour integration, and convergence of Dirichlet series all sit
behind [03-classical-analysis.md](03-classical-analysis.md), which has not
started.

Neither blocker touches the elementary material below them, and there is a
great deal of that left.

## Next five, in their priority order

- [ ] **1. The structure of (ℤ/n)\* and primitive roots.** Elementary,
      self-contained, reachable with the existing `ModEq` machinery, and the
      natural companion to Fermat and Euler. Their view: the most conspicuous
      hole in an otherwise complete elementary shelf.
- [ ] **2. Multiplicative arithmetic functions as a family.** Möbius, the
      divisor function, Dirichlet convolution, and multiplicativity proved
      once rather than per function. Unlocks inclusion-exclusion arguments and
      makes the existing totient work compose.
- [ ] **3. Unique factorization as a theorem, not a construction.** State and
      prove the fundamental theorem of arithmetic in the form "the
      factorization multiset is unique", now that `Nat.Multiset` exists. This
      is the bridge between the number theory shelf and the new combinatorics
      carriers.
- [ ] **4. Sums of two squares, with the descent argument reusable.** A named
      classical result that exercises Gaussian-integer reasoning without
      needing the ring structure, and whose descent method is worth having as
      a producer-visible pattern.
- [ ] **5. Chebyshev-type bounds on π(x).** The first genuinely analytic
      result reachable without complex analysis, using only elementary
      estimates on binomial coefficients — which this library already has.
      Their view: the cheapest possible proof that the analytic door is not
      permanently closed.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 1,218 proved ℕ/ℤ facts, 257 open. Wilson, quadratic reciprocity, Fermat, Euler totient, Bézout, CRT, Euclid, √2 irrational all present and axiom-free. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-7): `int_prelude/mult_order.rs`, 11 declarations with empty footprints — multiplicative order by bounded search, order divides the totient, `a^k ≡ 1 ↔ ord ∣ k`, primitive roots, and power injectivity (ADR-1598). **Existence of a primitive root mod a prime did not land**, and the obstruction is precise: the counting route needs `∑_{d∣n} φ(d) = n`, hence a divisor-set aggregate and the `d ↦ n/d` reindexing of a predicate-restricted sum, neither of which exists. Two design findings recorded: the search predicate must be shifted (`a^(j+1) ≡ 1`, since the unshifted form is true at j=0 for every a), and `Coprime (a^i) n` falls out of the order relation via the Bézout certificate already inside it. | `a9ef9465d`; `int_prelude::` 87 passed |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); fr = (d.get('formal') or {}).get('fragment')
    if fr in ('Nat', 'Int'): c[d.get('epistemic_status')] += 1
print(c)
PY

# does a named result exist? search the SHAPE, and rebuild first
cargo run --release -p axeyum-lean-kernel --example shape_search -- --const Nat.totient
just brief "primitive root"
```

## Related

- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the ℤ
  categoricity result and the least-number-principle work
- [04-algebra.md](04-algebra.md) — the `Quot.sound` blocker in full
- [07-combinatorics.md](07-combinatorics.md) — `Nat.Multiset` and `Nat.Finset`
