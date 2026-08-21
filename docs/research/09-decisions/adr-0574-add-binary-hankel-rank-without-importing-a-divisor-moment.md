# ADR-0574: Add binary Hankel rank without importing a divisor moment

Status: accepted
Date: 2026-08-20
Index-summary: Add bounded GF(2) Hankel rank characteristics while keeping the prime-weighted higher-moment residue explicit

## Context

The one-sided relative trace `(REL)` remains the sole open statement in the
paper-facing Lemire proof.  The strongest still-unimported fixed-base-field
moment technology is Yiasemides's Hankel-matrix treatment of divisor sums in
short intervals.  Its setting includes `q=2`, and the Lemire interval has free
dimension just above half the polynomial degree, where the published divisor
variance calculation has especially simple lower-skew-triangular matrices.

Axeyum previously had an integer Hankel determinant for detecting short
Frobenius-trace recurrences.  It did not have the finite-field rank invariant
used in this method: for a sequence `alpha_0,...,alpha_n`, the balanced Hankel
rank and its `(rho,pi)` characteristic, with quasi-regularity `pi=0`.

## Decision

Add `binary_hankel_characteristic` as a bounded native `GF(2)` operation.  It
returns the balanced matrix dimensions, exact rank, `rho`, `pi`, initial-zero
count, and quasi-regular verdict.  Charge matrix construction and elimination
against the existing deterministic `Gf2Limits` ceilings.  Check every binary
sequence of length at most nine against an independent row-span enumeration,
and retain explicit empty, degree, and work-limit declines.

Do **not** promote the published divisor variance theorem, triangular endpoint
geometry, or a measured Hankel stratum to proof credit for `(REL)`.  A future
Hankel bridge receives endpoint credit only after it retains the signed
von-Mangoldt/Mobius weights and proves the required aggregate estimate.

## Evidence

Yiasemides computes a second moment of the divisor function `d_2`.  The source
explicitly says that even the next higher-moment extension requires counting
additively constrained triples of Hankel sequences and reduces only the cases
where not all truncated sequences are quasi-regular.  The all-quasi-regular
sector remains.  In its discussion of fourth moments of Dirichlet
`L`-functions, the source likewise leaves three simultaneous requirements:
rank characteristics, a kernel equation, and the rank characteristics after
truncation.

The Lemire target is different twice over: it is a fourth moment (or the still
weaker one-sided trace `(REL)`) of the polynomial von Mangoldt population, not
the second moment of `d_2`; and substituting `Lambda=mu*deg` creates the signed
cross-convolution-order terms already isolated by ADR-0543 and ADR-0544.
Hankel triangularity does not remove those signs.  Thus the new primitive
closes a real CAS representation gap but the source theorem does not close a
mathematical proof gap.

Primary source:

- C. Yiasemides, *The variance and correlations of the divisor function in
  `F_q[T]`, and Hankel matrices*, especially the higher-moment remark following
  the kernel-structure theorems and the fourth-moment discussion,
  <https://arxiv.org/abs/2110.05959>.

## Consequences

- Fixed-`q` Hankel experiments no longer need SymPy or an ad hoc rank routine.
- A rank-only or divisor-only report remains diagnostic and cannot discharge
  `(REL)`.
- The smallest credible Hankel continuation is a signed count of the residual
  all-quasi-regular Mobius strata.  If it merely reconstructs the existing
  cross-order convolution, effort returns to the collective Witt/localized
  trace route rather than accumulating more moment tables.
- The manuscript's red warning remains mandatory.
