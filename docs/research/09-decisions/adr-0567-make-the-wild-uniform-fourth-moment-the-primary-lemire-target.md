# ADR-0567: Make the wild uniform fourth moment the primary Lemire target

Status: accepted
Date: 2026-08-20
Index-summary: Translate Hast--Matei exactly, retain its degree-dependent constant and low-characteristic limits, and expose the uniform wild estimate needed at q=2

## Context

[Hast--Matei, Theorem 1.4](https://arxiv.org/abs/1604.02067) proves for fixed
`m,n,h` and growing `q=p^r`

```text
E_f |sum_(deg g<=h) (Lambda(f+g)-1)|^m
    <= C_(m,n,h) q^((h+1)(m-1)),
```

assuming `p>n` when `m>2`.  At a Lemire endpoint put
`H=2^(n-ell)=2^(h+1)`.  The short-interval summand is the class discrepancy
`D_e`, and therefore the `m=4` conclusion is exactly

```text
M_4 <= C_(4,n,h) 2^ell H^3.
```

The proper-power-aware endpoint ledger needs

```text
M_4 < (H-P_n)^4.
```

Thus the exact sufficient constant is

```text
C_(4,n,h) < (H-P_n)^4 / (2^ell H^3).
```

It tends to `2` at the odd endpoint and `4` at the even endpoint.  This is a
precise bridge, but not a published endpoint theorem: Hast--Matei explicitly
fix `n,h`, allow the implicit constant to depend on them, take `q` to infinity,
and exclude `p=2` here.  Merely removing `p>n` while retaining an uncontrolled
`C_(4,n,h)` would not imply Lemire.

Their Remark 1.5 identifies nontrivial `S_n^m` action on cohomology as the
source expected to improve `H^(m-1)` toward `H^(m/2)`.  At fixed `q=2`, that
equivariant cancellation or an algebraic substitute is also what must make the
constant degree-uniform.  [Yiasemides's fixed-`q` Hankel
method](https://arxiv.org/abs/2110.05959) is adjacent but
does not supply this result: its primary theorem is divisor-function variance,
and its higher-moment section explicitly leaves the rank-of-sums problem open.

## Decision

Treat the following as the primary analytic target:

> Prove the characteristic-two fourth-moment estimate
> `M_4 <= C 2^ell H^3` at both Lemire endpoints with the exact
> proper-power-adjusted constant inequality above, uniformly in `ell`.

Record two distinct obligations, neither of which may be suppressed:

1. replace the tame singular-locus argument in characteristic two; and
2. obtain an effective degree-uniform equivariant trace bound with a small
   enough explicit constant.

The CAS weak-moment ledger exposes `2^ell H^3` and the exact rational allowed
constant.  It proves only the translation and endpoint implication.

Also tighten the even proper-power envelope.  Odd exponents `k>=3` contribute
nothing: odd powering is an automorphism of the principal-unit 2-group and,
because `n/k<=ell`, forces the putative irreducible to be `x^(n/k)`.  The
surviving layers give

```text
P_(2ell+2) <= (ell+1) 2^ceil(ell/2)
              + (2ell+2) 2^ceil((ell+1)/2).
```

## Consequences

- The bridge consolidates the fourth-moment and equivariant-trace routes, but
  it does not make the proof close.
- A theorem with an unspecified constant depending on `n,h` receives no
  endpoint credit.
- The exact even strong-target crossover moves from `ell=17` to `ell=13`.
- Support-only hypercontractivity and the existing Hankel variance theorem
  remain diagnostics, not substitutes for the wild uniform estimate.
- No universal fourth-moment estimate or Lemire theorem is established here.
