# ADR-0509: Reject positive four-phase complementarity for the connected Witt sum

Status: accepted
Date: 2026-08-19
Index-summary: Test the four primitive modulo-eight phases by exact integer autocorrelation and retain their indefinite Gauss cancellation

## Context

ADR-0508 retains the four primitive additive modulo-eight phases whose checked
Gauss combination reconstructs the connected signed Witt spectrum.  Full
Fourier support does not rule out a weaker useful identity: the four phases
might form a complementary family whose summed spectral power is flat.

For the phase population `n_r(a)` above Witt class `a`, put

```text
u_r(a)=n_r(a)-n_(r+4)(a),  0<=r<4,
C(s)=sum_r sum_a u_r(a)u_r(a+s).
```

The Ramanujan sum over the four odd residues modulo eight gives the exact
integer identity

```text
sum_(j=1,3,5,7) T_j*T_j^* = 4 C.
```

Thus the phases are complementary exactly when `C(s)=0` for every nonidentity
shift, equivalently when `sum_s C(s)^2=C(0)^2`.

## Decision

Compute `C(0)`, the largest off-identity `|C(s)|`, and `sum_s C(s)^2` inside
the connected Witt report.  Use this exact test to reject positive
four-phase complementarity before applying Cauchy--Schwarz across phase
sectors.  Preserve the signed, indefinite Gauss combination in subsequent
experiments.

## Evidence

At `(ell,k,d)=(9,11,8)`, the exact report gives

```text
C(0)                    = 13942624
max_(s != 0) |C(s)|     = 10785296
sum_s C(s)^2            = 5227607974543488.
```

The off-identity maximum is about `0.7735 C(0)`, and the square sum is about
`26.89 C(0)^2`, rather than exactly `C(0)^2`.  The connected signed spatial
second moment is only `126568`, so the positive four-phase channel at the
identity is over one hundred times larger than the signed channel.  A pinned
regression checks all three integers, while an independent two-point mutation
turns an exactly complementary delta into a function with nonzero
off-identity mass.

## Alternatives

- Bounding the sum of the four spectral powers was rejected because it
  destroys the cross-phase signs responsible for the checked Gauss
  reconstruction.
- Declaring a Heisenberg rank on the collapsed phase functions remains
  rejected: no affine-domain group law or associative central-extension
  cocycle has been supplied.

## Consequences

- A Golay/supplementary complementary-family theorem cannot explain even the
  pinned endpoint-tail witness.
- More unrestricted phase support or positive spectral-power tables are
  deprioritized.
- A viable joined-domain construction must retain indefinite cross-phase
  cancellation and the affine-fibre variables.  If no natural associative
  cocycle emerges, the next analytic target is the connected
  fourth-cumulant/gcd stratification.
- This is a bounded negative diagnostic and grants no endpoint theorem credit.
