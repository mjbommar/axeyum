# Number Theory

> Layer 3 · destinations · decidability: `bounded` · axeyum theory: BV / LIA · status: `covered`

## What it is

The study of the integers: **primes** and factorization, **congruences**,
**Diophantine equations** (integer solutions to polynomial equations), and
landmark theorems — infinitude of primes, the fundamental theorem of arithmetic,
Fermat's little theorem, Euler's theorem, the Chinese remainder theorem.

## Role in the tour

A destination, and the most *decidable-friendly* of the three: its
computational core (gcd, modular arithmetic, linear Diophantine) is exactly what
axeyum decides today, so it is the first destination with a self-checking
exercise family.

## Prerequisites

- [Divisibility & the Euclidean Algorithm](../02-structures/divisibility-and-euclid.md)
- [Modular Arithmetic & Congruences](../02-structures/modular-arithmetic.md)
- [Mathematical Induction](../00-foundations/induction.md)
- [Counting & Combinatorics](../02-structures/counting.md)

## Unlocks

(Destination.)

## Testable in axeyum

**Covered** by `Family::NumberTheory`. The bounded/computable core self-checks
oracle-free: Bézout's identity (witness from extended Euclid), modular inverses,
parity facts, and linear Diophantine (un)solvability (GCD test). Bounded
instances of the famous theorems — Fermat's little theorem at a fixed prime,
factorization of a fixed `n` — are checkable by computation + verification.

Example exercises (`Family::NumberTheory`):
- `bezout_identity(w, a, b)` — `a·x + b·y = gcd(a,b)`, witnessed.
- `modular_inverse(w, a)` — `a·a⁻¹ ≡ 1 (mod 2ʷ)`, witnessed.
- `consecutive_product_even(w)` — `k·(k+1) ≡ 0 (mod 2)`, exhaustive `unsat` of the negation.
- `square_parity(w)` — `x² ≡ x (mod 2)`, exhaustive.

## Proved in the kernel — general, quantified, axiom-free

**This section corrects what stood here before.** The paragraph below used to
read: *"The universal theorems — infinitely many primes, FTA in general,
Fermat/Euler for all `a`, quadratic reciprocity — require induction/quantifiers
and are Lean-horizon."* Measured against a freshly built
`shape_search --include-constructed` on 2026-08-30, **three of those four are
landed in the in-tree Lean kernel, general and axiom-free**:

| classical theorem | kernel declaration | axioms |
|---|---|---|
| Infinitely many primes | `Nat.exists_prime_gt`, `Int.euclid_infinitude` | 0 |
| Fundamental theorem of arithmetic (**existence half**) | `Nat.exists_prime_factorization` | 0 |
| Euclid's lemma (the uniqueness half's engine) | `Nat.euclid_lemma` | 0 |
| Fermat's little theorem, all `a` | `Nat.pow_prime_modeq_self` | 0 |
| Euler's totient multiplicativity | `Nat.totient_mul_of_coprime`, `Nat.totient_prime_pow` | 0 |
| Wilson's theorem, **both directions** | `Int.wilson`, `Int.wilson_converse`, `Int.wilson_iff` | 0 |
| Euler's criterion | `Int.euler_criterion_pm_one` | 0 |

Read these from the kernel, not from this table — it is a snapshot:
`prelude_theorem_inventory --release --include-constructed`.

## Still Lean-horizon, and why

- **Quadratic reciprocity** — genuinely absent (control: `Int.euler_criterion_pm_one`,
  `Int.is_quadratic_residue` both FOUND by the same method). The Legendre symbol
  at a fixed `p` is decidable by Euler's criterion, so the *decidable fragment*
  is cheap; the reciprocity law itself is unbuilt.
- **Euler's theorem `a^φ(n) ≡ 1 (mod n)`** — absent, though both residue-permutation
  ingredients (`Int.euler_unit_coprime`, `Int.euler_unit_injective`) are landed.
- **Uniqueness of prime factorization** — blocked by the kernel's *type theory*,
  not by decidability: there is no `List`, `Finset`, product type or quotient by
  permutation in which to state multiset equality. The expressible reformulation
  (multiplicity agreement at each prime, via `Nat.countRange_permute`) is
  reachable today. See ADR-0716's **row 2′**.
- Analytic number theory (prime counting, Dirichlet, Chebyshev) is out of scope
  for this ladder entirely.

## Graded-family treatment

Number theory's families — with their row 2 identified, and the reason most of
them have none — are in
[`../graded-statement-families-number-theory-and-linear-algebra.md`](../graded-statement-families-number-theory-and-linear-algebra.md).
The short version, decided in
[ADR-0716](../../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md):
`Nat.le_total` is a **proved theorem** here, so the decision principle every
real-analysis boundary result extracts is already available and no
number-theoretic statement can reduce to it. The subject's one genuine boundary
is the unrestricted least-number principle, which reduces to full excluded
middle.

## References

- Hardy & Wright, *An Introduction to the Theory of Numbers*.
- axeyum: `axeyum-scenarios::number_theory`, `prove_lia_unsat_by_gcd`.
