# 01 — Number theory

Reviewer: an elementary and analytic number theorist
Verdict, 2026-09-04: **impressed, with a visible ceiling**
Last measured: 2026-09-04 at `1856cdb3c`

> "This is a real library. It is also 1830s number theory, and you have built
> it so well that the wall it hits is now unmistakable."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

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
  no arithmetic functions as a family. **[AUDIT] Totient multiplicativity IS
  proved in exactly the general form this bullet denied**:
  `Nat.totient_mul_of_coprime`, landed `05ad19d54` 2026-08-30 (audit row A7).
- ~~**Primitive roots and the structure of (ℤ/n)\*.**~~ **[AUDIT] landed
  2026-09-04** (roadmap W1-7), except existence modulo a prime.
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

- [x] **1. The structure of (ℤ/n)\* and primitive roots.** *Landed 2026-09-04 except existence mod a prime; see the progress log.* Elementary,
      self-contained, reachable with the existing `ModEq` machinery, and the
      natural companion to Fermat and Euler. Their view: the most conspicuous
      hole in an otherwise complete elementary shelf.
- [~] **2. Multiplicative arithmetic functions as a family.** — *aggregate, reindexing, convolution and multiplicativity landed 2026-09-05; Möbius inversion sized.* Möbius, the
      divisor function, Dirichlet convolution, and multiplicativity proved
      once rather than per function. Unlocks inclusion-exclusion arguments and
      makes the existing totient work compose.
- [x] **3. Unique factorization as a theorem, not a construction.** **[AUDIT]
      Already proved**: `Nat.Multiset.count_eq_of_prod_eq` with
      `exists_prime_factorization` (audit row A5). Original framing: This
      is the bridge between the number theory shelf and the new combinatorics
      carriers.
- [~] **4. Sums of two squares, with the descent argument reusable.** — *descent step, the identity, and the mod-4 refutation landed 2026-09-05; Fermat's theorem itself waits on an ℤ order shelf.* A named
      classical result that exercises Gaussian-integer reasoning without
      needing the ring structure, and whose descent method is worth having as
      a producer-visible pattern.
- [~] **5. Chebyshev-type bounds on π(x).** — *primorial and the sharp central-binomial bound landed 2026-09-05; the π(x) statements themselves are a never-scored held-out family and are deliberately untouched.* The first genuinely analytic
      result reachable without complex analysis, using only elementary
      estimates on binomial coefficients — which this library already has.
      Their view: the cheapest possible proof that the analytic door is not
      permanently closed.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 1,218 proved ℕ/ℤ facts, 257 open. Wilson, quadratic reciprocity, Fermat, Euler totient, Bézout, CRT, Euclid, √2 irrational all present and axiom-free. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-7): `int_prelude/mult_order.rs`, 11 declarations with empty footprints — multiplicative order by bounded search, order divides the totient, `a^k ≡ 1 ↔ ord ∣ k`, primitive roots, and power injectivity (ADR-1598). **Existence of a primitive root mod a prime did not land**, and the obstruction is precise: the counting route needs `∑_{d∣n} φ(d) = n`, hence a divisor-set aggregate and the `d ↦ n/d` reindexing of a predicate-restricted sum, neither of which exists. Two design findings recorded: the search predicate must be shifted (`a^(j+1) ≡ 1`, since the unshifted form is true at j=0 for every a), and `Coprime (a^i) n` falls out of the order relation via the Bézout certificate already inside it. | `a9ef9465d`; `int_prelude::` 87 passed |
| 2026-09-05 | **Next Five item 2 partly landed** (roadmap W2-18, ADR-1619): the divisor-set aggregate `sumDivisorsBy`, its reindexing primitive, `numDivisors`, `IsMultiplicative` with the totient as an instance, and Dirichlet convolution with commutativity — 29 declarations, footprint 0. The obstruction ADR-1598 named for primitive-root existence is half closed: the aggregate and reindexing exist; the classification of `[0,n)` by `gcd k n` does not. **The reindexing map this reviewer and every brief assumed, `d ↦ n/d`, is not the one that works** — it is not injective on the range — and the involution fixing non-divisors is. Möbius inversion did not land and is sized: it needs the divisors of a squarefree number in bijection with subsets of its prime factors. | `3e650f81a`; `nat_prelude::` 562 passed |

| 2026-09-05 | **Item 4, first slice** (roadmap W3-10, ADR-1633): `Int.IsSumOfTwoSquares`, the Brahmagupta–Fibonacci identity emitted by the ring producer rather than proved by hand, closure under multiplication, the mod-4 refutation, and a reusable descent step shaped for `Nat.strongInduction`; 20 declarations, footprint 0. **Fermat's theorem is open on order, not algebra**: ℤ has no `natAbs_le_iff`, `mul_le_mul`, or `sq_le_sq`, so the strict decrease of the descent measure cannot yet be stated. The reviewer's blocker was wrong in one place: −1 as a residue mod `p ≡ 1 (mod 4)` was already proved (ADR-1235). | `e5c1d09cd` |
| 2026-09-05 | **Item 5, first slice** (roadmap W3-11, ADR-1637): `Nat.primorial` with its equations and monotonicity, and `choose (2m+1) m ≤ 4^m`, sharper than the existing power-of-two bound; 15 declarations, footprint 0. Erdős's `primorial n ≤ 4^n` is open on a divisibility law for predicate-restricted products. **The π(x) bounds were not attempted and should not be briefed**: five rows of the held-out family `discrete-step-and-counting-bounds` are that shelf and the family has never been scored; two of its rows are one lemma application away, which is a fact about the evaluation, not a task. | `88ee63a0e` |

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
