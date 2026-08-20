# ADR-0560: Stop the fixed modulo-eight odd-endpoint route

Status: accepted
Date: 2026-08-20
Index-summary: Refute universal modulo-eight nonvanishing at degree 55 and return the endpoint proof to a genuine aggregate estimate

## Context

ADR-0559 retained the finite pattern

```text
I_(2ell+1)(1) != 0 mod 8
```

as an explicitly conjectural stopping target.  A single zero residue was the
declared termination condition.  The uniqueness-bounded one-prime endpoint
program made the next rows feasible without weakening exactness.

## Decision

Stop the fixed modulo-eight route.  At `ell=27`, degree `55`, the exact result
is

```text
N_55(1) = 268616921,
Delta_(27,55) = 181465,
I_55(1) = (N_55(1)-1)/55 = 4883944 = 0 mod 8,
v_2(I_55(1)) = 3.
```

The arithmetic cross-checks internally:

```text
2^(55-27) + 181465 = 268616921,
1 + 55 * 4883944 = 268616921.
```

This is a counterexample to the universal congruence, not to Lemire's
existence conjecture: the same row contains 4,883,944 requested irreducibles.
Do not replace modulo eight by another fixed modulus merely because the first
27 rows avoid it.  Under the natural random-residue heuristic, fixed
two-adic nonvanishing should eventually fail at every fixed precision unless
an actual structural valuation bound is proved.

The exact Carlitz 2-rank and Newton machinery from ADR-0559 remains useful as
a diagnostic, but no longer leads to an odd-endpoint theorem through `(C8)`.
Return theorem effort to a genuine aggregate trace estimate (or to an
explicit, proved degree-dependent residue law), and require any proposed
congruence to predict this degree-55 counterexample before further fleet work.

A primary-source applicability check also narrows the proposed Newton-polygon
literature bridge.  Kramer--Miller's *p-adic estimates of abelian Artin
L-functions on curves* assumes `p>=3`, and Kramer--Miller--Upton's *Newton
polygons of sums on curves I* opens with `p` odd.  Part II treats
`Z_p`-towers.  Davis--Wan--Xiao likewise treats a `Z_p`-tower, while the
higher-rank Ren--Wan--Xiao--Yu extension has Galois group the unramified
coefficient ring `Z_(p^a)`, not the finite product of cyclic 2-groups in the
binary Hayes tower.  These papers provide nearby language and possible proof
technology, but none states the needed binary product-group theorem.

## Evidence

The exact single-NTT computation ran on `s4` for 4,217.201 seconds with peak
RSS 30,417,756 KiB and exit status zero.  Its executable and complete timing
log have SHA-256 hashes

```text
0a505ec4360069c868999d5c00819f2e31721d83fdbfc8086e27f56ad4d3cea2
1567140e8a0875ab55514ddacb8d114c235818a0dcea2830b1e5ffc4906e7744
```

The program admits its single transform residue only after the proved
odd-endpoint candidate-count bound makes that residue the unique possible
integer.  The output is therefore an exact exhaustive row, not a probabilistic
primality or floating-point calculation.

## Consequences

- `F:gf2-lemire-odd-endpoint-modulo-eight-nonvanishing` is refuted by the
  degree-55 witness.
- Zero 2-rank remains correct but supplies no endpoint existence theorem.
- Characterwise Newton slopes remain too weak; their aggregate cancellation
  is once again an estimate to prove, not a route to fixed-modulus positivity.
- The universal Lemire theorem and the requested final paper remain open.

## References

- J. Kramer--Miller, [*p-adic estimates of abelian Artin L-functions on
  curves*](https://arxiv.org/abs/2006.04936).
- J. Kramer--Miller and J. Upton, [*Newton polygons of sums on curves I:
  local-to-global theorems*](https://arxiv.org/abs/2110.08656) and [part
  II](https://arxiv.org/abs/2110.08657).
- C. Davis, D. Wan, and L. Xiao, [*Newton slopes for Artin--Schreier--Witt
  towers*](https://arxiv.org/abs/1310.5311).
- R. Ren, D. Wan, L. Xiao, and M. Yu, [*Slopes for higher rank
  Artin--Schreier--Witt towers*](https://arxiv.org/abs/1605.02254).
