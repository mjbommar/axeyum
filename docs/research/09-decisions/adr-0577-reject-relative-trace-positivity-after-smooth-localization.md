# ADR-0577: Reject relative-trace positivity after smooth localization

Status: accepted
Date: 2026-08-20
Index-summary: Pin exact negative connected traces and prevent smooth unit local terms from being mistaken for relative positivity

## Context

ADR-0576 proves that the odd-endpoint projective `Frob*c` fixed locus is
smooth, transverse, and has local intersection multiplicity one.  This makes
each individual fine-level point count nonnegative for the obvious geometric
reason.  The paper's remaining quantity `(REL)`, however, is the virtual
difference

```text
C_(ell,n) = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1),
a = ell-ceil(log2 ell)-1.
```

A tempting but invalid continuation is to infer `C_(ell,n)>=0` from the unit
local terms at the two levels.

## Decision

Add a pinned native sign control and reject relative-trace positivity.  Exact
class populations give

```text
C_(5,11) = -608,
C_(7,16) = -4608.
```

The first is an odd endpoint, where ADR-0576 simultaneously certifies smooth
transverse unit local terms.  Thus the negative sign is not produced by a
singular local correction: it arises because `(REL)` subtracts two different
positive fixed-point sums with different normalization.

Retain the genuinely one-sided statement `C>-B`; do not strengthen it to
`C>=0`, do not replace the relative virtual trace by either positive point
count separately, and do not assign numerical credit to local smoothness.

## Evidence

- `connected_relative_trace_is_not_sign_definite_after_smooth_localization`
  reconstructs both populations through the native recurrence and pins the
  two exact negative integers.
- The same test checks that the underlying identity populations remain
  positive and that the degree-11 projective fixed locus has status
  `SmoothTransverseUnitTerms` while its global trace-bound flag remains false.
- The existing refinement identities independently reconstruct `C` both from
  its Haar increments and from the two endpoint populations.

## Consequences

- Smooth fixed-point localization removes local pathologies but cannot prove
  `(REL)` by positivity.
- The remaining theorem must compare the two levels globally, preserving
  cancellation in their virtual difference.
- Further geometry receives endpoint credit only if it supplies a numerical
  lower bound for that relative trace.
