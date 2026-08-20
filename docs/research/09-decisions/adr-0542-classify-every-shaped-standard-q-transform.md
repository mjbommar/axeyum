# ADR-0542: Classify every shaped standard Q-transform

Status: accepted
Date: 2026-08-20
Index-summary: Use self-reciprocity and the Dickson invariant to prove that the cubic-to-sextic example is the only irreducible half-shaped source and output pair for the standard characteristic-two Q-transform

## Context

ADR-0530 checked the standard characteristic-two transform

```text
Q(f)(x)=x^n f(x+x^-1)
```

and rejected its published indefinitely iterated family as a universal Lemire
induction.  That did not exclude a different sequence of specially chosen
half-shaped sources.  A doubling construction would be especially valuable
because odd Capell substitutions preserve the desired coefficient window but
cannot change the 2-adic valuation of the degree.

## Decision

Add `characteristic_two_q_shape_obstruction`.  Every degree-`2n` Q-transform
is monic, constant-one, and self-reciprocal.  If its nonleading terms all have
degree at most `n`, self-reciprocity also removes every term below degree `n`.
Therefore a shaped irreducible output is forced to be

```text
x^(2n)+x^n+1;
```

omitting the middle term would give the square `(x^n+1)^2`.

Let `D_n` be the binary Dickson polynomial defined by

```text
D_0=0, D_1=x, D_n=xD_(n-1)+D_(n-2).
```

The invariant identity `D_n(x+x^-1)=x^n+x^-n` makes `D_n+1` the unique
possible source.  Reconstruct that source under explicit degree/work bounds
and check its Q-image against the forced trinomial exactly.

## Evidence

If `n` is even, characteristic two gives

```text
D_n+1=(D_(n/2)+1)^2,
```

so the source is reducible.  If `n` is odd, the coefficient of `x^(n-2)` in
`D_n` is one.  For `n>=5`, this exceeds `floor(n/2)` and the source is not
half-shaped.  Only `n=3` remains, giving

```text
x^3+x+1  ->  x^6+x^3+1.
```

Independent Rabin certificates check both exceptional polynomials.  Ordinary
tests replay the Dickson/Q identity and structural classification for every
`2<=n<=64`, and tight limits decline before work.

## Consequences

- The standard Q-transform has exactly one irreducible half-shaped
  source/output pair; no alternative choice of sources can turn it into an
  all-degree doubling induction.
- This strengthens ADR-0530 from rejection of one iterated theorem to a
  complete structural classification of every shaped standard Q-image.
- A constructive proof still needs a genuinely different degree-changing
  transform, while the selected analytic frontier remains fixed-`GF(2)`
  cancellation across the endpoint class sum.
