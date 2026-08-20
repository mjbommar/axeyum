# ADR-0538: Bound generalized Fomenko restriction packets before using them in the endpoint trace

Status: accepted
Date: 2026-08-20
Index-summary: Close coefficient-zero restriction fibres under cyclotomic Galois action, reconstruct their integral traces exactly, and reject a one-square-root-unit packet bound

## Context

Fomenko's three-coefficient argument restricts a Hayes character to the
subgroup with first coefficient zero.  For a fixed three-coefficient problem
this gives a surjective map with a small kernel and an explicit quadratic
`L`-polynomial formula.  A proposed Lemire bridge was to retain the first
active coordinates of a growing Witt group and seek the same compression.

The group map and the trace estimate are different obligations.  For
`1<=t<ell`, let `H_t` be the principal units congruent to one modulo
`x^(t+1)`.  Restriction to `H_t` has kernel the inflated character group of
`E_t`, of order `2^t`.  A raw restriction fibre is generally cyclotomic, not
rational, so treating its two NTT residues as one signed integer would be
invalid.

## Decision

Add `hayes_fomenko_restriction_packet_report`.  It closes every primitive
restriction fibre under odd-power cyclotomic Galois action, reconstructs the
resulting integral packet trace with two independent NTT primes, and requires
all packets to recover the independently computed exact-conductor trace.
Every packet is checked against the ordinary characterwise Weil envelope.
The explicit work bound

```text
2^ell * 2^t * exponent(E_ell)
```

is admitted before packet enumeration.

Test both Fomenko's one-coordinate choice `t=1` and the endpoint-matched
logarithmic choice

```text
t=min(ceil(log2 ell)+1,ell-1).
```

Do not credit the candidate that every rational packet trace has magnitude at
most one square-root unit `2^ceil(n/2)`.

## Evidence

For both endpoint parities through `ell=12`, the packets partition all
`2^(ell-1)` primitive characters and their signed traces reproduce the exact
conductor layer.  At `(ell,n)=(12,26)`, `t=1` gives 256 packets of size at
most 8.  Of these, 233 exceed one square-root unit; the maximum is 226816
against 8192, requiring coefficient 28.  The sum of packet absolutes is
15422336, while their signed total is 933888.

The logarithmic choice `t=5` gives 32 packets of size at most 64.  Of these,
29 exceed one square-root unit; the maximum is 525056, requiring coefficient
65.  The sum of packet absolutes is 6433280, while the same signed total is
933888.  A one-cell-below work limit declines before enumeration.

Gorodetsky's exposition of Fomenko shows why the fixed-level result is
stronger: at level three the restriction data feed an explicit degree-two
`L`-polynomial identity.  Surjectivity and a small kernel alone do not provide
an analogue of that identity as the conductor grows.

## Consequences

- The generalized restriction is an exact, reusable rational trace
  decomposition, but taking absolute values packet by packet still loses
  substantial cancellation.
- The logarithmic kernel reduces packet count without producing a uniform
  one-unit trace bound.  It does not prove the connected top-conductor target.
- A useful Fomenko generalization must prove new cross-packet orthogonality or
  uniformly controlled `L`-factor formulas; the group quotient by itself is
  bookkeeping.
- The Ito--Takeuchi--Tsushima Heisenberg formula remains a template rather
  than an imported estimate: it begins with a quadratic
  `y^2+y=xR(x)` phase for linearized `R`, while the checked joined Lemire
  phases have genuine higher mod-eight degree.
