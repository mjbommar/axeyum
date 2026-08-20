# ADR-0566: Classify and bound power-of-two compositions

Status: accepted
Date: 2026-08-20
Index-summary: Prove the exact composition-shape classification, add certificate-retaining substitution search, and distinguish isolated 64-to-512 successes from a nonexistent demonstrated 8-to-64-to-512 chain

## Context

A review sweep proposed nonmonomial polynomial composition as a constructive
power-of-two family.  It reported positive compositions at degrees 64 and
512 and summarized them as an iterating `8 -> 64 -> 512` family.  Before
granting construction coverage, both the universal shape claim and the
claimed chain must be checked inside Axeyum.

Let `f=x^n+q` be half-degree shaped and let `sigma=x^k+t` be monic, with
`s=deg(t)`.  Since

```text
deg(q(sigma)) <= k floor(n/2) <= floor(kn/2),
```

the shape of `f(sigma)` depends only on `sigma^n-x^(kn)`.  If
`lambda=2^v2(n)` is the least binary place of `n`, the characteristic-two
Frobenius expansion has distinct degrees and its unique largest proper term
has degree

```text
kn-(k-s)lambda.                                    (C)
```

Thus a nonmonomial substitution preserves shape exactly when

```text
(k-s)lambda >= ceil(kn/2).                         (S)
```

For `n=2^a m`, `m` odd, `(S)` is impossible when `m>=3`; when `m=1`, it is
equivalent to `s<=floor(k/2)`.  Therefore:

```text
f(sigma) is shaped
iff sigma=x^k, or n is a power of two and sigma is shaped.
```

## Decision

Expose:

- `polynomial_compose`, a resource-bounded Horner operation;
- `composition_shape_criterion`, which returns both `(C)/(S)` and the
  equivalent power-of-two classification, then checks them against the
  direct composition;
- `search_shaped_compositions`, which enumerates every nonmonomial shaped
  substitution of caller-selected degree and retains only outputs carrying a
  freshly produced and replay-checked Rabin certificate;
- `axeyum-gf2-composition-tower`, a bounded backtracking driver that accepts
  either a committed artifact or explicit packed source words.

Search is not theorem evidence.  The shape classification is proved by the
displayed distinct-degree Frobenius expansion.  Every irreducibility result
is separately certified.

## Evidence

The classification is checked on all 62 monic substitutions of degrees one
through five and source degrees one through fourteen: 868 map/degree cells.
It is additionally checked across all 5,580 shaped source polynomials in the
degree-at-most-eight subdomain, confirming that the verdict is independent of
the lower source coefficients.  Mutation controls pin a non-power-of-two
rejection, a power-of-two/shaped acceptance, a power-of-two/unshaped
rejection, the monomial branch, and a candidate ceiling.

The exact two-step octuple search then exhausts all shaped degree-eight
polynomials and all 31 nonmonomial shaped degree-eight substitutions at each
step:

```text
shaped irreducible degree-8 sources        2
certified degree-64 first-step hits        4
certified degree-512 continuations         0
```

Hence the review's data show that *some* degree-eight source reaches degree
64 and that *other, independently sampled* degree-64 sources reach degree
512.  They do not exhibit an iterated chain.  The stronger synthesis phrase
`8 -> 64 -> 512` is refuted for repeated degree-eight substitution starting
from any shaped degree-eight source.

## Consequences

- The composition-shape classification is now a proved Axeyum capability.
- Nonmonomial composition cannot help any source degree with odd part at
  least three.
- The finite positive compositions remain valid isolated witnesses, but no
  inductive power-of-two family is established.
- Pushing an isolated degree-512 witness to 4096 would add finite evidence,
  not prove the missing universal step.  It is therefore deprioritized.
- Construction cannot cover arbitrary odd prime degrees through this window;
  the all-degree proof still requires the aggregate analytic theorem or a
  genuinely new prime-degree construction.
