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
- A sentence in Gao, Howell, and Panario's 1999 survey says that Hsu's theorem
  permits the lower or higher "half" of the coefficients to be fixed. The
  explicit bound is not an endpoint existence theorem for fixed `q = 2`.
  Car's restatement of Hsu gives, for `k` prescribed leading coefficients and
  no trailing congruence,

  ```text
  n I(n; k) >= q^(n-k) - (1-q^(-k))(k+3)q^(n/2).
  ```

  At `k = ceil(n/2)-1` this lower bound is negative for all sufficiently large
  `n` when `q = 2`. Thus the survey's informal "half" must not be cited as a
  proof of this conjecture. See Hsu,
  [The Distribution of Irreducible Polynomials in
  F_q[t]](https://doi.org/10.1006/jnth.1996.0139), and Car's explicit
  [restatement](https://eudml.org/doc/207235).
- Gao, Kuttner, and Wang's exact Hayes-class formulas reach the relevant
  parameter boundary and are the best current attack surface:
  [Counting irreducible polynomials with prescribed coefficients over a finite
  field](https://arxiv.org/abs/2109.02000). Gao's later
  [improved error bounds](https://arxiv.org/abs/2109.14154) still do not prove
  positivity here. With `ell = ceil(n/2) - 1`, `q = 2`, and the identity type-II
  class, the main term and the published absolute error are of the same
  exponential order; the coefficient multiplying the error is too large.
- Gao's 2023 follow-up obtains existence with *roughly* half the coefficients
  prescribed, including positions near the middle, but does not state the exact
  all-degree fixed-`GF(2)` endpoint needed here: [New Estimates and Existence
  Results About Irreducible Polynomials and Self-Reciprocal Irreducible
  Polynomials with Prescribed Coefficients Over a Finite
  Field](https://doi.org/10.1007/s44007-023-00062-1).

### Exact integral specialization

Complex characters are not required to state the exact recurrence. Let

```text
E_ell = (1 + x GF(2)[x]) / (x^(ell+1))
S_ell = sum_{epsilon in E_ell} epsilon
A_d   = sum_{f monic, deg f = d} <f>  in Z[E_ell].
```

The coefficient classes are injective below `ell` and uniform from `ell`
onward, so

```text
A_d = sum of the 2^d represented classes,       d < ell,
A_d = 2^(d-ell) S_ell,                          d >= ell.
```

For `A(z) = sum A_d z^d`, define
`Lambda(z) = z A'(z) / A(z) = sum Lambda_d z^d`. Comparing coefficients in
`Lambda(z) A(z) = z A'(z)` gives the exact group-ring recurrence

```text
Lambda_n = n A_n - sum_{i=1}^{n-1} Lambda_i A_(n-i).
```

Unique factorization gives its coefficient meaning:

```text
[epsilon] Lambda_n
  = sum_{d | n} d *
      #{P monic irreducible : deg P = d, <P>^(n/d) = epsilon}.
```

Consequently the identity-class irreducible count is recovered recursively by
subtracting the proper-divisor terms and dividing by `n`. This is an exact,
integer-only version of the Hayes-class formula and a useful falsifier for any
proposed cancellation lemma. It is not yet a positivity proof.

Here `ell` counts prescribed zero coefficients. The conjecture's boundary is
therefore degree `2 ell + 1` in the odd case and `2 ell + 2` in the even case.
An independent implementation of the recurrence and direct Rabin enumeration
agree on the identity-class counts through degree 20:

```text
n:      3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19  20
count:  1  1  1  2  3  2  4   7  4 12  6 19 20 28 33 59 49 101
```

The signs of the deviation from the equidistributed main term vary, so a proof
cannot assume that every nontrivial-character contribution has a favorable
sign. The first theoretical work item is now sharper: bound the *aggregate*
properly weighted nontrivial contribution in the identity class at degrees
`2 ell + 1` and `2 ell + 2`, or replace it with a construction. Any claimed
bound must be checked for strict positivity, not merely asymptotic main-term
dominance.

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
