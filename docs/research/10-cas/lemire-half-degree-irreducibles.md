# Lemire half-degree irreducibles: theorem and Axeyum research contract

Status: active research
Date: 2026-08-18

## Exact target

For every integer `n >= 1`, prove that there is a monic irreducible
`f in GF(2)[x]` of degree `n` such that

```text
deg(f - x^n) <= floor(n / 2).
```

This is the conjecture stated in section 4.1 of Lemire and Kaser,
[Strongly universal string hashing is fast](https://arxiv.org/abs/1202.4961).
The social-post phrase "less than `floor(n/2)`" cannot be the all-degree
theorem: at `n = 2` it permits only `x^2 + 1`, which is reducible.  All Axeyum
claims and experiments use the paper's non-strict bound.

The application is a sparse high half: reduction by `f` replaces `x^n` with a
polynomial of degree at most `floor(n/2)`, making the correction step in
Barrett-style binary-polynomial reduction cheap.

## Reciprocal reformulation

Put `m = floor(n/2)` and let

```text
f(x) = x^n + q(x),    deg q <= m.
```

Its reciprocal `g(x) = x^n f(1/x)` is irreducible exactly when `f` is and
satisfies

```text
g(x) == 1 (mod x^(n-m)) = 1 (mod x^ceil(n/2)).
```

Conversely, every monic irreducible degree-`n` polynomial in that residue class
reciprocates to a polynomial of the required form.  The conjecture is therefore
equivalent to the existence, in every degree, of a prime polynomial in the
identity ray class modulo `x^ceil(n/2)`.

This lemma is elementary and should be the first lemma in a short paper.  It
also explains the difficulty: the prescribed-coefficient interval is exactly
at the half-degree boundary, where general short-interval estimates over fixed
`GF(2)` do not immediately give positivity.

## Backward proof plan for a paper under five pages

1. State the exact theorem and prove the reciprocal equivalence.
2. Prove a single central counting or construction lemma: for every `n`, a
   degree-`n` irreducible is `1 mod x^ceil(n/2)`.
3. Discharge any finite exceptional range with independently checked Axeyum
   certificates, and state the exact checker and artifact hashes.
4. Apply reciprocity and give the Barrett-reduction corollary.

The missing mathematics is step 2.  Numerical verification, including Arndt's
reported range through 400, is evidence about the conjecture but is not that
lemma.

## Literature boundary

- Lemire's [MathOverflow question](https://mathoverflow.net/questions/81717/)
  records the problem and its relationship to prescribed coefficients and
  short intervals.
- Bank, Bary-Soroker, and Rosenzweig prove a prime-polynomial theorem in short
  intervals in the large-field regime, not the required fixed field
  `q = 2`: [Prime polynomials in short intervals and in arithmetic
  progressions](https://arxiv.org/abs/1302.0625).
- Pollack's prescribed-coefficient results do not reach this fixed-field
  half-degree boundary: [Irreducible polynomials with several prescribed
  coefficients](https://arxiv.org/abs/1601.06867).
- Gao's exact Hayes-class formulas and improved error terms reach the relevant
  parameter boundary and are the best current attack surface, but their crude
  absolute error bound does not by itself prove positivity at `q = 2`:
  [Counting irreducible polynomials with prescribed coefficients over a finite
  field](https://arxiv.org/abs/2109.14154).

The first theoretical work item is to specialize Gao's group-algebra formula
to the identity class of the principal-unit group
`1 + x GF(2)[x] / x^(ell+1)`, and seek cancellation or an exact recurrence at
degrees `2 ell` and `2 ell + 1`.  Any claimed bound must be checked for strict
positivity, not merely asymptotic main-term dominance.

## Axeyum boundary and evidence ladder

The research becomes a proper Axeyum component in stages:

1. **CAS value layer:** bounded bit-packed `GF(2)[x]` arithmetic.
2. **Certificate layer:** Rabin Frobenius-chain and Bezout certificates; search
   is untrusted and the checker derives the complete degree factorization.
3. **Artifact layer:** canonical serialization, semantics version, producer
   identity, limits, witness, certificate, checker outcome, and content hash.
4. **Independent layer:** a second small checker implementation and exhaustive
   small-degree differential tests; completion-only fleet jobs receive no
   credit.
5. **Formal layer:** encode reciprocity and the central lemma in the Lean
   kernel path, with any finite computation represented by checked evidence and
   an explicit axiom footprint.
6. **Ledger layer:** only then establish a fact for the universal theorem;
   bounded verified ranges remain separate facts with finite statements.

No finite-field SMT sort is added merely to host the experiment.  A solver
surface becomes justified only with explicit term semantics, total operations,
model lifting, replay, and proof evidence under the foundational DAG.
