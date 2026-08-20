# ADR-0565: Generalize Capell to all odd monomial rays

Status: accepted
Date: 2026-08-20
Index-summary: Replace the cubic-only construction audit by the full odd-monomial criterion, including odd seed degrees, composite powers, iteration, incompatible-prime controls, and independent finite replay

## Context

ADR-0531 admitted the cubic construction `f(x^3)` and correctly classified
its 138 eligible witnesses through degree 400.  It then stated that monomial
rays omit every odd degree.  That conclusion is true only for the fixed power
three: `3` divides `2^d-1` only when `d` is even.

The classical binomial irreducibility criterion is not cubic-specific.  Let
`f` be irreducible of degree `d`, let `alpha` be a root of `f`, and put
`Q=2^d-1`.  For any positive integer `k`, `f(x^k)` is irreducible exactly
when `x^k-alpha` is irreducible over `GF(2^d)`.  Over a binary field this
forces `k` odd, and for every prime `p|k` the remaining condition is

```text
alpha^(Q/p) != 1.                                  (Np)
```

Indeed `(Np)` says that the `p`-part of `ord(alpha)` exhausts the `p`-part of
`Q`.  This is equivalent to the radical and cofactor conditions in the
standard finite-field binomial theorem.  The exceptional `4|k` clause cannot
arise because `Q` is odd.  The criterion is classical; see Lidl and
Niederreiter, *Finite Fields*, the binomial irreducibility theorem, together
with Capell's composition lemma.  Reis's primary-source discussion also
states the three binomial conditions explicitly in the source of
<https://arxiv.org/abs/1905.07798>.

## Decision

Expose `monomial_composition_criterion` for arbitrary bounded `k`.  It:

1. replay-checks the source Rabin certificate;
2. factors `k` into distinct primes;
3. computes every applicable residue `(Np)` exactly in `GF(2)[x]/(f)`;
4. returns the formal composition and a criterion verdict.

Also expose `monomial_prime_eligibility`.  It performs one prime-local test
without allocating `f(x^p)`, allowing very large degree rays to be audited
under ordinary polynomial-work limits.  The cubic API remains as a compatible
wrapper around the general operation.

Generalize `axeyum-gf2-capell-audit` with `--prime-limit`.  The new mode
searches odd primes only, requires a deliberately incompatible prime to fail
for every source, and independently Rabin-checks every positive composition
whose output degree is at most 256.  Larger outputs receive only the exact
prime-local theorem criterion; they are not mislabeled as direct Rabin
certificates.

Odd monomial substitution preserves half-degree shape.  The construction
also iterates for every fixed odd `k`: for `p|k`, if `beta^k=alpha`, then

```text
v_p(ord(beta)) = v_p(ord(alpha)) + v_p(k),
v_p(2^(dk)-1)  = v_p(2^d-1)      + v_p(k)
```

by the order formula and odd-prime LTE.  Thus every `(Np)` renews at the next
stage, and one eligible seed supplies all degrees `d*k^j`, `j>=0`.

## Evidence

Focused tests pin:

- the odd seed `x^3+x+1` with `k=7`, producing the shaped irreducible
  `x^21+x^7+1`;
- the primitive quartic with composite `k=15`, testing both primes `3,5` and
  directly Rabin-certifying the degree-60 output;
- rejection of incompatible powers `2,3,5` at the cubic seed;
- agreement of the legacy cubic wrapper with its established controls;
- CLI positive, negative, and incompatible-prime paths.

The generalized CLI was run on all 400 committed witnesses with every odd
prime at most 20,000,000, split across `s1,s4,s5,s6,s7`.  It found:

```text
eligible source witnesses       371 / 400
eligible odd source degrees     174 / 200
whole-composition dual checks    35
incompatible-prime controls     400 / 400 rejected
```

This independently corrects a review-sweep estimate of `367/172`; the larger
native census is `371/174` at the stated identical cutoff.  A separate
Python implementation using integer bit-polynomials—not Axeyum's quotient
arithmetic—rechecked primality, `p|(2^d-1)`, and all 371 residues `(Np)` with
zero disagreements.  The census is finite evidence and search-cutoff
dependent; the criterion and iteration are the universal theorem.

## Consequences

- ADR-0531 remains correct for `k=3`, but its claim that monomial rays omit
  every odd degree is superseded.
- Axeyum now carries the full theorem-backed monomial construction family,
  rather than one cubic specialization.
- These rays still do not cover arbitrary degrees: within the finite audit,
  29 seed witnesses (including 26 odd degrees) have no eligible prime below
  the cutoff.  Across all degrees the union of fixed-base rays has no known
  all-degree coverage theorem.
- The next constructive obligation is the non-monomial power-of-two
  composition window; this increment does not claim Lemire's conjecture.
