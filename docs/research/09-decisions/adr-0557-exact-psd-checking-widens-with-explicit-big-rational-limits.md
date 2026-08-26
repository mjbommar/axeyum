# ADR-0557: Exact PSD checking widens with explicit BigRational limits

Status: accepted
Date: 2026-08-25
Index-summary: Add bounded arbitrary-precision LDL-style PSD decisions that decline on dimension or coefficient growth rather than overflowing

## Context

Axeyum's SOS checker already decides positive semidefiniteness by exact rational symmetric
elimination, including the subtle zero-pivot case.  Its scalar type is the IR's checked
`i128` rational, so coefficient overflow correctly returns no verdict.  Certification lane
5a targets dual slack matrices as large as 2,000 by 2,000, where exact elimination can grow
far beyond `i128` even when the source entries are modest.  Replacing the existing checker or
silently promoting only selected operations would make its resource/trust behavior unclear.

## Decision

Retain `sos::psd::is_psd` as the compact checked-`i128` route and add
`sos::psd_big::is_psd_big` as an explicit arbitrary-precision route.  The wide checker uses
`BigRational` throughout and has three mandatory admission controls:

- maximum matrix dimension;
- maximum total numerator/denominator bytes in the input; and
- maximum numerator or denominator bit length of any elimination intermediate.

Exceeding any control returns `BigPsd::Declined` with the observed resource and configured
limit.  It is neither PSD nor non-PSD.  Malformed, asymmetric, negative-pivot, and forbidden
zero-pivot inputs return `BigPsd::No` only when exact arithmetic establishes that result.
Successful results report every nonzero pivot, the number of zero pivots, and the measured
maximum intermediate bit length.

This component checks the PSD obligation of a supplied exact dual matrix. It does not create
that matrix, validate problem-specific affine dual constraints, or transform floating solver
output into a rigorous rational point; those are separate producer and envelope obligations.

## Evidence

- A diagonal matrix with 81-digit integer entries succeeds beyond the `i128` ceiling.
- A singular rank-one Gram matrix succeeds with one zero pivot.
- An indefinite symmetric control returns `No`.
- A one-bit intermediate policy returns `Declined` rather than a mathematical verdict.
- Focused tests and warning-denied Clippy pass for all CAS targets.

## Alternatives

### Replace `Rational` globally with `BigRational`

Rejected.  It would widen the IR trusted base and change performance/serialization for every
solver route to solve one explicitly large artifact class.

### Retry automatically after `i128` overflow

Rejected.  Hidden promotion obscures which resource policy and checker implementation
accepted an artifact.  Callers must select the wide route and record its limits.

### Accept floating eigenvalues with a tolerance

Rejected.  The target is an exact independently checkable certificate; a numerical solver
status and tolerance recreate the authority boundary the lane is meant to remove.

## Consequences

- Exact theta/SDP certificate work no longer has an arithmetic-width blocker in Axeyum.
- A 2,000-row artifact remains subject to potentially large cubic work and coefficient growth;
  the defaults admit the dimension but do not promise completion.
- The next 5a component must bind a graph, objective, rational dual data, affine feasibility,
  rounding margin, and this PSD outcome in one portable certificate envelope.
