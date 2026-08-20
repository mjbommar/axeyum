# ADR-0526: Do not refine Sawin's nonequivariant vanishing-cycle bound by long-cycle type

Status: accepted
Date: 2026-08-19
Index-summary: Require an equivariant smoothing or a direct twisted fixed-locus theorem before applying Sawin's square-locus support bound to the long-cycle component

## Context

Sawin's short-interval variety `X_(n,m,c)` carries an `S_n` action, and the
von Mangoldt virtual character is supported on long cycles.  This makes it
tempting to combine two correct statements:

1. the singular locus at infinity maps, in characteristic two, into the locus
   whose root polynomial is a polynomial in `u^2`; and
2. the von Mangoldt virtual representation evaluates a cohomology
   representation at one long cycle.

The tempting conclusion is a recursion from `(n,m)` to
`(floor(n/2),floor(m/2))` on the long-cycle part of cohomology.  Sawin's proof
does not provide such a recursion.

His vanishing lemma deforms the defining complete intersection
`(F_1,...,F_m)` to a generic one `(G_1,...,G_m)`.  The generic `G_i` are not
symmetric, so the total family and its vanishing-cycle triangle are not
`S_n`-equivariant.  The argument proves an ordinary support and degree bound;
it cannot be projected onto an `S_n` character after the fact.

There is a second independent gap.  The logarithmic-derivative argument shows
only that the image of the bad locus at infinity under the finite quotient map
lies in the coefficient subspace supported in even degrees.  It neither
identifies the bad locus with a smaller short-interval variety nor controls
the ranks, monodromy, or long-cycle traces of the vanishing-cycle stalks on
that support.  In characteristic two the quotient map is also wildly ramified
along the repeated-root locus, precisely where this argument is supported.

## Decision

Do not infer a cyclic-eigenspace Betti bound, a Frobenius--long-cycle trace
bound, or a recursion in half-sized parameters from Sawin's singular-support
dimension estimate alone.

A future Sawin-based proof receives theorem credit only after supplying one of:

1. an explicit `S_n`-equivariant smoothing together with an equivariant
   vanishing-cycle calculation on the binary square locus;
2. a direct bound for the Frobenius-weighted long-cycle trace on the original
   singular family; or
3. an identified recursive complex, including stalk multiplicities and the
   induction/restriction maps that relate its cyclic character to the
   half-sized problem.

The exact identity between the Mangoldt population and the
Frobenius--long-cycle trace remains valid.  It is a compression of the target,
not an estimate for it.

## Evidence

- Sawin's Lemma 2.5 chooses a generic complete intersection in its smoothing
  step and uses only that the vanishing-cycle complex is semiperverse and
  supported on the bad locus.
- Sawin's Lemma 2.4 obtains the square condition only after applying the finite
  symmetric quotient map to the affine cone over the bad locus at infinity.
- His later `S_n` action is asserted on the cohomology of the original fibre;
  no `S_n` action is constructed on the generic deformation used in Lemma 2.5.
- The Grothendieck--Lefschetz trace of Frobenius composed with a long cycle is
  exactly the original Mangoldt population, so evaluating that fixed locus
  without a new estimate is circular.

## Consequences

- The partition-scale coherent Koszul trace is retained only as motivation;
  it is not transferred to compactly supported etale cohomology.
- No CAS endpoint ledger may substitute a conjectural cyclic Betti constant
  into Sawin's weight exponent and label the result proved.
- The live routes remain a genuinely equivariant long-cycle theorem, the
  connected Witt/Carlitz trace bound, or the connected fourth-cumulant bound.

