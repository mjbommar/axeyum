# ADR-0535: Bound the binary power-sum character sector before importing high-trace symmetry

Status: accepted
Date: 2026-08-20
Index-summary: Prove that binary monomial power-sum characters reach at most the thin primitive quadratic sector and none of every even conductor layer

## Context

Gorodetsky--Kovaleva obtain cancellation beyond the generic conductor range
for the special character

```text
chi_(k,psi)(f)=psi(p_(-k)(f)).
```

Their Lemma 3.8 rewrites its von-Mangoldt sum over degree `n` by replacing
`k` with `gcd(k,2^n-1)`.  The proof uses that the maps `x -> x^k` and
`x -> x^gcd(k,2^n-1)` have the same image and kernel on
`GF(2^n)^times`.  The Lemire conductor trace instead sums every primitive
Hayes character, and the connected fourth moment couples four independently
varying characters subject to one product constraint.  Importing the special
symmetry therefore first requires a coverage audit.

## Decision

Add `hayes_power_sum_character_coverage`.  Over `GF(2)` the unique
nontrivial additive character has values in `{+1,-1}`, so every
`chi_(k,psi)` has order at most two and every product of such characters
remains quadratic.  Moreover Frobenius gives `p_(-2m)=p_(-m)`, so a single
monomial character is primitive at level `k` only when `k` is odd.

The mixed-radix Hayes group enumeration independently checks the exact
primitive quadratic count

```text
Q_j = 2^((j-1)/2)  if j is odd,
      0             if j is even,
```

against all primitive characters, whose count is `2^(j-1)`.  The
multiplicative span of all binary monomial power-sum characters through level
`j` can cover at most `Q_j`; equality is not assumed.  At level 11 this upper
bound is `32/1024`, while at level 12 it is `0/2048`.

## Consequences

- Lemma 3.8's monomial image/kernel symmetry cannot be extended to the whole
  primitive Hayes family by multiplication or Galois closure.
- Every even conductor layer is entirely outside the binary quadratic
  power-sum sector.  Since the selected Carlitz trace and conductor Haar
  cumulant use both parities, discarding those layers is not an endpoint proof.
- Gorodetsky--Kovaleva's general-character estimate remains an individual
  bound.  Summing it over the family loses the exponential family factor and
  does not prove the connected fourth-cumulant target.
- The live target remains a representation acting on the complete
  higher-Witt character family before absolute values: the connected
  cumulant/conductor-Haar inequality, or an equivalent relative trace bound.

