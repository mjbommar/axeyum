# ADR-0549: Close the level-three extension trace by period-24 symmetry

Status: accepted
Date: 2026-08-20
Index-summary: Derive the exact ell-three degree-seven class distribution from Gorodetsky's characteristic-two period-24 theorem and refute the one-extra-q connected Adams cutoff repair

## Context

ADR-0548 found the exact minimum normalized connected-trace coefficients

```text
q=2,4,8,16: 1,10,58,250.
```

The `q=16` row refuted the original coefficient `ell^4=81`, while the weaker
allowance `ell^4 q` survived that finite row.  Extrapolating again would repeat
the same mistake unless the level-three trace could be evaluated symbolically.

Gorodetsky, *Irreducible polynomials over F_(2^r) with three prescribed
coefficients* ([arXiv:1805.07105](https://arxiv.org/abs/1805.07105)), Theorem
1.1, proves that

```text
f_q(n,t_1,t_2,t_3)
  = (psi_q(n,t_1,t_2,t_3)-q^(n-3))/q^(n/2)
```

has period 24 and supplies its power-map symmetry.  This is an exact theorem
for every `q=2^r`, not a large-field estimate.

## Decision

Apply the theorem with `n=7`.  Since `gcd(7,24)=1` and
`7^(-1)=7 mod 24`, while

```text
binom(7,2)=binom(7,3)=1 mod 2,
```

the symmetry gives

```text
f_q(7,t_1,t_2,t_3)
  = f_q(1,t_1,t_2+t_1^2,t_3+t_1^3).
```

There is one degree-one monic polynomial with a specified first coefficient
and none unless its next two padded coefficients vanish.  Substitution into
the definition of `f_q` therefore proves

```text
N(t_1,t_2,t_3)
  = q^4-q+q^3  if t_2=t_1^2 and t_3=t_1^3,
    q^4-q      otherwise.
```

There are `q` special classes and `q^3-q` ordinary classes.  Their deviations
from the uniform mean `q^4` are `q^3-q` and `-q`, respectively.  Direct
expansion gives

```text
M_2 = q^5(q^2-1),
M_4 = q^5((q^2-1)^4+(q^2-1)),
K_4 = q^10(q^2-1)(q^4-6q^2+6),
T_r = q^16(q^2-1)(q^4-6q^2+6).
```

Add `binary_extension_ell_three_degree_seven_closed_form` to the native CAS.
Exact enumeration over `GF(2)` and `GF(4)` checks every population moment;
the formula independently reproduces all six integers from the 100-shard
`GF(16)` merge.  Resource and zero-degree rejection remain fail closed.

The trace has `q`-degree 22.  Removing the Adams weight `q^(2n)=q^14`
leaves degree 8, two degrees above the proposed `2ell=6` cutoff and one above
the one-extra-`q` repair.  An explicit finite failure occurs at `q=128`:

```text
ceil(abs(T_r)/q^20) = 16378 > 81*128 = 10368.
```

## Consequences

- Both the original and one-extra-`q` universal level-three cutoff hypotheses
  are refuted.  Neither may enter the endpoint paper or fact dependencies.
- No `q=32`, `q=64`, or `q=128` enumeration is needed; the exact formula is
  stronger and cheaper than those fleet experiments.
- This fixed-level obstruction does not refute a different geometric estimate
  whose allowed weight or coefficient depends explicitly on `ell`, and it
  does not address the separate binary Witt or signed cross-order targets.
- Fomenko--Gorodetsky compression is exact and powerful at three prescribed
  coefficients, but Gorodetsky proves that the normalized periodicity fails
  from four coefficients onward.  It is therefore a stopping theorem for this
  shortcut, not the missing growing-conductor endpoint theorem.
