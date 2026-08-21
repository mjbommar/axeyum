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
| Prescribed leading block | zero coefficients `x^(n-1),...,x^ceil(n/2)` | [Pollack](https://www.pollack-math.net/prescribed.pdf) | Uniform theorem is strictly below half: `s+t <= (1/2-epsilon)n`. |
| Exact prescribed-prefix formulas | Artin--Schreier curve point counts | [Granger](https://arxiv.org/abs/1610.06878) | In characteristic two, general formulas stop before the growing half-length prefix. |
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

## Closed edges: what the graph does and does not reduce

The reciprocal/Fourier translation itself is not an open gap.  The native
`inverse_additive_mobius_spectrum` checks, for every admitted finite row,

```text
sum_(u in V_d) M_k(u^(-1))
  = 2^(d-ell) sum_(a in W_d^perp) H_k(a),
```

including inversion as a permutation, Walsh Parseval, every convolution order,
and the ramified reciprocal convention.  The exact order-by-order regrouping
also retains the signed cancellation that would be destroyed by absolute
values.  This closes the change-of-variables edge to the inverse-additive
literature, but proves no uniform bound.

The existing characteristic-two Bagshaw audit closes the next tempting edge:
the proven inverse-energy and wild-Kloosterman inputs give genuine savings in
some Type-I/II ranges, but pointwise estimates reach only the far tail (even
the ideal zero-epsilon exponent pair begins at `d > 14 ell / 15 + O(1)`).
The full loss-aware endpoint ledger has no strict uniform row at `ell=300`.
So a direct Vaughan port cannot be upgraded to `(HWO)` by improving the
reciprocal bookkeeping or by treating the Fourier identity as an asymptotic
theorem.

Accordingly the remaining bridge has a sharply delimited form: establish
collective cancellation across the high-Witt, exact-order signed family before
absolute values.  It must be a new theorem about that family, rather than a
quadratic-form identification, a fixed-field pointwise estimate, or a
rephrasing of the inverse-energy bound.

## Prescribed-coefficient boundary

Lemire is the endpoint leading-block prescription: after reciprocal reversal,
it fixes `ceil(n/2)-1` consecutive coefficients.  Pollack's Proposition 10
(quoting the Hayes/Hsu/Car line of work) is uniform over all finite fields only
for `s+t <= (1/2-epsilon)n`, with `epsilon>0` fixed.  Its displayed error is
of Weil size and therefore cannot establish the equality case at `q=2`.

This is not repaired by the characteristic-two exact-formula literature.
Granger's general method requires fewer prescribed coefficients than the
characteristic; its binary computations treat small fixed prefixes, while the
half-degree prefix grows with `n`.  Thus the familiar prescribed-coefficient
theorems translate correctly to `(L)`, but leave exactly the endpoint that
Lemire asks for.  They are evidence for the formulation, not a hidden proof.

## Use

For every new source, first classify its asymptotic axis, translate its
observable to the signed identity-class trace, and price its constant against
`(HWO)`. The live obligation is stated in
[lemire-high-witt-expert-brief.md](lemire-high-witt-expert-brief.md).
