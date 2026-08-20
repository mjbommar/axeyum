# ADR-0530: Bound characteristic-two Q-transforms without promoting a universal Lemire induction

Status: accepted
Date: 2026-08-20

## Context

The Lemire lane has certified shaped irreducibles through degree 400, but a
finite sparse pattern is not an all-degree construction.  The bridge audit
identified Kyuregyan's characteristic-two recurrent constructions as a cheap
independent avenue.  The exact transform equations must be checked before a
recurrence is treated as a proof route.

## Decision

Add a bounded native `characteristic_two_q_transform` operation to the GF(2)
CAS, while keeping transformed irreducibility as a separate certificate
obligation and rejecting the standard indefinitely iterated Q-transform
theorem as a universal Lemire induction.

For `Q(f)(x)=x^n f(x+x^(-1))`, Axeyum expands `(x^2+1)^i` by Lucas submasks,
checks input/output degree ceilings, and charges every produced term against a
deterministic work limit.  The polynomial type separately exposes the exact
non-strict half-degree shape predicate.

## Evidence

The coefficient identity

```text
[x^(2n-1)] Q(f) = [x^(n-1)] f
```

is immediate from the transform.  Over GF(2), the standard recurrent
irreducibility hypotheses require the coefficient on the right to be one, so
the transformed polynomial has a forbidden upper-half term.  A shaped input
of degree greater than two instead has that coefficient zero and lies outside
the theorem's hypotheses.

Focused mutation controls establish the narrower truth.  The operation maps
`x^3+x+1` to the independently certified irreducible shaped polynomial
`x^6+x^3+1`; its next iterate violates the shape.  A theorem-hypothesis input
`x^4+x^3+x^2+x+1` produces an independently certified irreducible degree-eight
output with its forced degree-seven term.  Tight work and degree limits return
typed declines.

The related cyclotomic family
`Phi_(3^r)=x^(2*3^(r-1))+x^(3^(r-1))+1` gives infinitely many Lemire degrees,
but does not cover arbitrary degrees.

## Alternatives

Promoting the recurrence from its irreducibility theorem without checking the
coefficient window was rejected: its defining trace coefficient is precisely
the forbidden transformed coefficient.  Rejecting every isolated Q-transform
was also rejected because the cubic-to-sextic control is a genuine success.

## Consequences

Axeyum can now audit further characteristic-two transform proposals with exact
polynomial identities and independent Rabin certificates.  This closes the
standard Q-transform as the missing universal construction while retaining
honest credit for special degree families.  The endpoint proof still requires
the connected Hayes/Witt cancellation lemma or another all-degree argument.

ADR-0542 subsequently strengthens this boundary: self-reciprocity and the
Dickson invariant classify every shaped standard Q-image, proving that the
cubic-to-sextic example is the only irreducible shaped source/output pair.
