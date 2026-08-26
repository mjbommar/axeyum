# ADR-0560: Theta duals are reconstructed from the graph

Status: accepted
Date: 2026-08-26
Index-summary: Check exact Lovasz theta clique bounds by reconstructing the dual slack from the graph and sparse nonedge multipliers

## Context

ADR-0557 widened exact PSD decisions to bounded arbitrary-precision rationals, but a PSD
matrix alone proves no optimization bound. Certification target 5a requires the matrix to be
the slack of the exact graph relaxation whose objective bounds the clique number. Accepting a
producer-supplied slack without re-deriving it would leave the graph, objective, and affine
dual constraints outside the checked boundary.

The published Krpan--Povh code uses the standard clique theta primal: maximize `<J,X>` over
PSD `X`, with `trace(X)=1` and `X_ij=0` for every graph non-edge. Its dual has objective `t`
and slack `t I + Y - J`, where `Y` is supported only on non-edges. A PSD slack establishes
`omega(G) <= theta(G) <= t` by weak duality.

## Decision

Add `sos::theta::check_theta_clique_dual`. The input graph is a symmetric loop-free Boolean
adjacency matrix. The certificate contains an exact rational bound and sparse, canonical,
unique non-edge multipliers. The checker:

1. validates the graph shape and semantics;
2. rejects out-of-range, non-canonical, duplicate, or edge-supported multipliers;
3. independently reconstructs every entry of `t I + Y - J`; and
4. invokes ADR-0557's bounded exact BigRational PSD checker.

Malformed or exactly non-PSD data are `Rejected`; admission-limit exhaustion is `Declined`;
only an exact PSD result is `Verified`. Omitted non-edge multipliers mean zero. No numerical
tolerance, solver status, rounded objective, or producer-supplied slack is accepted.

## Evidence

- The exact `K_3` dual verifies bound 3, while the false bound 2 is rejected.
- The empty three-vertex graph verifies bound 1 with unit non-edge multipliers.
- Edge-supported, reversed, out-of-range, and duplicate multipliers are rejected.
- Asymmetric graph data are rejected, while a dimension policy produces `Declined` rather
  than a mathematical result.

## Consequences

- A future 5a artifact can bind the graph and rational dual data to the exact claimed bound;
  a detached PSD matrix is no longer enough.
- The checker does not recover the dual matrix discarded by the published solver, nor does it
  rationalize floating output. That producer remains the immediate target blocker.
- Exact elimination may remain cubic and resource-intensive at order 2,000. Limits describe
  what was admitted; they do not promise the target will fit.
