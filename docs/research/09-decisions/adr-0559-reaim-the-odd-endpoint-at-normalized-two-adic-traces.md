# ADR-0559: Re-aim the odd endpoint at normalized two-adic traces

Status: superseded by ADR-0560
Date: 2026-08-20
Index-summary: Promote modulo-eight nonvanishing as the bounded odd-endpoint target while proving that Carlitz p-rank zero alone lacks the required normalized precision

The stopping target selected here was refuted at `ell=27`; see ADR-0560.  The
precision audit and exact Newton-polygon conclusions remain valid.

## Context

The analytic and connected-trace routes reach the same endpoint square-root
barrier: individual Weil bounds retain a factor asymptotic to `ell`.  The exact
odd endpoint instead has

```text
N_(2ell+1)(1)=1+(2ell+1) I_(2ell+1)(1).             (OR)
```

Consequently any fixed-power congruence that makes `I_(2ell+1)(1)` nonzero
would bypass that barrier.  Exact rows suggested the candidate

```text
I_(2ell+1)(1) != 0 mod 8.                           (C8)
```

An external re-aim review proposed deriving such a congruence from the
Deuring--Shafarevich `p`-rank formula for the Carlitz tower.  That proposal
must first be checked at the precision actually required by `(C8)`.

## Decision

Retain `(C8)` as an explicitly unproved odd-endpoint target and expose every
bounded exact row through `odd_endpoint_two_adic_report`.  The report records
the residues modulo 8 and 16, the exact `2`-adic valuation, and the associated
Carlitz point-count precision ledger.

For the binary Carlitz field of conductor `t^(ell+1)`, the Galois group has
order `2^ell`; the finite place `t` is totally ramified and infinity splits.
Deuring--Shafarevich therefore gives

```text
gamma(C_ell)-1
  = 2^ell (gamma(P1)-1) + (2^ell-1)
  = -1,
gamma(C_ell)=0.                                     (DS)
```

Thus the whole tower has `2`-rank zero.  This does **not** prove `(C8)`.  The
exact point-population identity and `(OR)` are

```text
#C_ell(GF(2^n)) = 1+2^ell N_n(1),
I_n(1) = ((#C_ell-1)/2^ell-1)/n,  n=2ell+1.         (PC)
```

Since `n` is a unit modulo eight, recovering `I_n(1) mod 8` requires the raw
point count modulo `2^(ell+3)`.  Equation `(DS)` controls only the slope-zero
part, equivalently the zeta numerator modulo two.  A proof must instead
control the normalized higher-slope trace through three further bits after
division by `2^ell`.  Deuring--Shafarevich may be an input to such a proof,
but is not the proof.

Do not infer an even-degree induction from the square proper-power stratum.
Identifying that stratum with a half-sized shaped count is exact bookkeeping;
it supplies neither the required strict inequality nor a congruence recurrence
for the new degree.  An even bridge receives credit only after that recurrence
is derived and checked.

Add `hayes_conductor_two_adic_newton_report` to test the sharper proposed
mechanism.  In `Z[zeta_(2^r)]`, two is totally ramified and `1-zeta` is the
unique uniformizer.  Repeated exact triangular division by `1-zeta` computes
each coefficient valuation; a rational lower convex hull then gives every
primitive-character Newton slope without a numerical root approximation.
Compare the resulting power-valuation floor with the independently computed
integral exact-conductor trace.

## Evidence

Every odd endpoint from degree 3 through degree 51 has now been evaluated
exactly.  The residues for `ell=1,...,25` are

```text
1,1,3,4,4,6,4,1,1,4,3,6,2,3,5,7,1,3,7,2,7,5,3,2,6 mod 8.
```

They are all nonzero and the largest observed `2`-adic valuation is two.
This is finite evidence only: under a random-residue baseline, avoiding zero
modulo eight for 25 rows is suggestive but not remotely a universal proof.

The two previously missing cheap rows are

```text
ell=20, n=41: N_n(1)=2100267, I_n(1)=51226 = 2 mod 8,
ell=21, n=43: N_n(1)=4173366, I_n(1)=97055 = 7 mod 8.
```

They were computed on `s5` and `s6` with the exact v3 binary SHA-256
`2218173d6356b812acc3a7c17c8706e9e3ae910618b15e0919467f65845ede42`.
The complete timing logs have SHA-256
`4673ae0ef398f4384b88272093d3078b0bcf38160326b9843570291385ebb9e9`
and `ef56e7958ca4ae2d6cd5945a7f66c55b04ccf892f2c47381f95ceb17046c54ef`.

Focused tests reconstruct the residue from the curve point count at exactly
`ell+3` bits, replay `(DS)` at every tested level, and pin every residue and
valuation through `ell=12`.  The independent two-prime identity-class route
continues to check the underlying exact counts.

The exact Newton experiment also rejects a second oversimplification: the
relevant roots are not confined to a thin near-half-slope window.  At odd
Frobenius degree `2j+1`, the minimum primitive-character slopes and their
total multiplicities are

```text
j                 2  3  4  5  6  7   8   9  10
minimum slope   1/2 1/2 1/4 1/4 1/4 1/4 1/8 1/8 1/8
multiplicity      2   8   8   8  64  80 128 128 256.
```

The corresponding exact conductor traces have `2`-adic valuations
`3,5,4,5,11,7,8,8,9`, all independently reconstructed from class
populations.  Thus slopes far below one half survive characterwise and cancel
only after the complete exact-conductor sum.  A useful theorem must control
that Galois/conductor aggregate; a characterwise minimum-slope cutoff simply
recreates the missing cancellation.

## Alternatives

- **Continue mining pointwise analytic bounds:** demoted.  The exact ledgers
  show that all current versions retain the same endpoint logarithm.
- **Treat `2`-rank zero as a modulo-eight trace theorem:** rejected.  It loses
  `ell+2` raw precision bits relative to `(PC)` and does not distinguish
  higher Newton slopes.
- **Discard all but a near-half Newton window characterwise:** rejected by
  exact slopes `1/4` from level four and `1/8` from level eight.  Their large
  multiplicities require aggregate cancellation before reduction.
- **Promote 25 nonzero residues to a theorem:** rejected.  The stopping table
  tests `(C8)`; it cannot establish it.
- **Claim the odd congruence would automatically settle even degrees:**
  rejected until an exact proper-power congruence recurrence is proved.

## Consequences

- The next algebraic target is one precise statement about the complete
  Galois/conductor aggregate of the low positive-slope Carlitz trace modulo
  eight, not a characterwise cutoff or another unrestricted spectrum.
- A counterexample residue zero terminates this route immediately without
  affecting the analytic or characteristic-delta reductions.
- A proof of `(C8)` settles every odd endpoint.  A separate checked recurrence
  is still required before it contributes to every even endpoint.
- The universal Lemire theorem and the requested final paper remain open.

## References

- M. Deuring and I. R. Shafarevich, the `p`-rank formula for `p`-group covers.
- M. Rosen, *Number Theory in Function Fields*, Chapters 9 and 12 and
  Proposition 16.7.
