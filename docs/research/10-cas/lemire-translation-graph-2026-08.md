# Lemire translation graph: exact target and bridge audit

Status: **research map, not a proof**

Date: 2026-08-21

## Invariant target

For `n >= 1`, Lemire asks for an irreducible `f=x^n+q` in `GF(2)[x]`
with `deg q <= floor(n/2)`. Reciprocity gives the exact equivalent problem

```text
there is a degree-n prime in 1 + x^ceil(n/2) GF(2)[x].                 (L)
```

A usable bridge must retain fixed `q=2`, the growing prime-power modulus,
and a constant strong enough for positivity at the equality boundary. A
large-field limit, fixed conductor, or linear conductor loss cannot prove
`(L)`.

## Translation graph

| Node | Exact translation | Resource | Endpoint status |
|---|---|---|---|
| Prime in reciprocal short interval | `(L)` | [Gorodetsky](https://arxiv.org/abs/1810.00483) | Fixed-field estimate lacks endpoint margin. |
| Hayes/ray-class Fourier family | identity class modulo `x^j` | [Gao--Kuttner--Wang](https://arxiv.org/abs/2109.02000) | Exact enumeration, not positivity. |
| High-Witt exact order | signed trace `T_(j,s)` | [Sawin](https://arxiv.org/abs/1805.04330) | Correct geometry, but published equidistribution is `q -> infinity`. |
| Factorisation function interval | connected von-Mangoldt trace | [Sawin](https://arxiv.org/abs/1809.05137) | Square-root mechanism requires relatively large characteristic. |
| Prime/Mobius correlations | Vaughan complete sums | [Gorodetsky--Sawin](https://arxiv.org/abs/1811.04834) | Large-`q` theorem; framework remains relevant. |
| Quadratic digits along primes | quadratic Type-I/II phase | [Cheng](https://arxiv.org/abs/2605.25877) | New candidate bridge below; theorem is odd-characteristic and fixed-band. |
| Sparse construction | trinomials/pentanomials/composition | [Handbook discussion](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf) | No all-degree construction theorem. |

## Candidate bridge: averaged reciprocal-symbol defects

Cheng's 2026 theorem proves fixed-field equidistribution for a **fixed-band**
quadratic digit form along irreducibles over an **odd** field. Its central
Type-I argument is notable: rather than demand a pointwise quadratic-rank
bound, it averages the rank defect after enlarging `P g g*` to the vector
space of reciprocal symbols.

This suggests the following precise binary research program:

```text
high-Witt signed family -> Vaughan factorisation -> reciprocal symbols
                         -> average a Galois-ring rank defect before abs values.
```

It is not a theorem transfer. The published polarization uses `2 != 0`; our
phases have squareful-input zeros and growing Witt depth. A valid bridge must
establish a Galois-ring replacement for the complete sums, a defect bound
uniform in the growing depth, and an endpoint ledger implying `(HWO)`.
The corrected fibre calculations already rule out treating its all-points
square mass as a literal nonpositive four-point correlation.

There is also a concrete stop condition for a direct quadratic-form port. In
the independent level-nine fibre census, all 2,518 zero-free sampled fibres
were classified as nonquadratic (and none as quadratic). This is finite
evidence, not a theorem about all levels, but it rules out claiming that the
present phase is already Cheng's quadratic digit phase. Any successful bridge
must first identify a different Galois-ring or higher-degree complete-sum
structure.

## Use

For every new source, first classify its asymptotic axis, translate its
observable to the signed identity-class trace, and price its constant against
`(HWO)`. The live obligation is stated in
[lemire-high-witt-expert-brief.md](lemire-high-witt-expert-brief.md).
