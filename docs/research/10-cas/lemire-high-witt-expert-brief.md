# Lemire high-Witt cancellation: exact theorem specification for expert review

Status: **open problem statement, not a proof**
Date: 2026-08-21
Scope: the only remaining analytic obligation in the Lemire half-degree
irreducible-polynomial lane after the verified low-order reduction.

## The problem after the proved reductions

For `ell >= 200` and `n in {2ell+1, 2ell+2}`, let

```text
E_j = (1 + x F_2[x]) / (x^(j+1)),
N_n(g) = sum_{f monic, deg f=n, class(f)=g} Lambda(f).
```

The desired irreducible polynomial is a prime in the identity ray class.  The
exact Haar telescope reduces its existence to the one-sided inequality

```text
C_(ell,n) > -B_(ell,n),                                      (REL)
C_(ell,n) = sum_{j=a}^ell 2^(j-1) H_j(1),
a = ell-ceil(log2 ell)-1,
B_(ell,n) = 2^(2ell) - 2^ceil(n/2) sum_{1<=j<a}(j-1)2^(j-1).
```

This implication, including proper-power handling and the degree-400 finite
handoff, is proved in the lane.  What is not proved is `(REL)`.

There is an exact order-resolved sufficient statement.  For `s >= 0`, define

```text
H_(j,s) = {chi in E_j^dual : chi^(2^s)=1},
h_(j,s) = |H_(j,s)| = 2^(j-floor(j/2^s)),
P_(j,s) = sum_{g in 2^s E_j} N_n(g),
T_(j,s) = h_(j,s)P_(j,s) - h_(j,s-1)P_(j,s-1)
           - h_(j-1,s)P_(j-1,s) + h_(j-1,s-1)P_(j-1,s-1).
```

Finite-group orthogonality proves this four-population identity: `T_(j,s)`
is the exact conductor-`j`, exact order-`2^s` Hayes trace.  It is not an
asymptotic approximation.

Put `c=ceil(log2 ell)` and let `Q` be the largest power of two satisfying
`3cQ <= ell`.  All layers with order at most `Q` are already paid by the
individual Weil bound.  The remaining theorem whose proof would close both
endpoints is:

> **High-Witt order-layer theorem (HWO).**  For every `ell >= 200`, both
> endpoint degrees `n`, every `a <= j <= ell`, and every nonempty exact-order
> layer with `2^s > Q`,
>
> ```text
> 4 ell |T_(j,s)(n)|
>   <= #X_(j,s) (j-1) 2^ceil(n/2),
> ```
>
> where `#X_(j,s)` is the exact number of conductor-`j`, order-`2^s`
> characters.

The endpoint ledger proves `HWO => REL =>` Lemire's conjecture.  The surviving
orders form only `O(log log ell)` bands at each conductor, but no known
argument establishes their cancellation.  At `ell=200`, 20 of the 67 initial
order layers are already discharged; only 47 high-order layers remain.

## Elementary symmetry audit: no free high-order zero

One possible shortcut is now ruled out exactly.  Let `q=2^s` and write

```text
c_j(q) = h_(j,s)-h_(j-1,s)
       = 2^(j-floor(j/q)) - 2^(j-1-floor((j-1)/q)).
```

This is the number of conductor-`j` characters of order dividing `q`; the
exact-order count is `c_j(q)-c_j(q/2)`.  If `q` divides `j`, the two powers in
`c_j(q)` agree, so `c_j(q)=0`.  Since `q/2` also divides `j`, the exact-order
count is then zero.  Therefore every nonempty exact-order/conductor layer has
`q` not dividing `j`.

This matters because the power-subgroup condition then forces the newly
exposed coefficient to be zero.  Writing

```text
Delta_(j,s) = 2 P_(j,s) - P_(j-1,s),
```

every nonempty layer is consequently in the forced regime and has the exact
form

```text
T_(j,s) = h_(j-1,s) Delta_(j,s) - h_(j-1,s-1) Delta_(j,s-1).
```

So the apparent `q | j` automatic cancellation cannot remove a charged
layer: it occurs only where that exact layer is empty.  A proof of `HWO` must
control this difference of two nested sparse-coefficient imbalances, rather
than exploit periodicity of the exposed coefficient.

There is a useful normalized version of the same statement.  Put

```text
d_s = floor((j-1)/2^s),
R_(j,s) = h_(j-1,s) / h_(j-1,s-1) = 2^(d_(s-1)-d_s).
```

For every nonempty layer, the exact character count is
`#X_(j,s)=h_(j-1,s-1)(R_(j,s)-1)`, while the preceding display gives
`T_(j,s)=h_(j-1,s-1)(R_(j,s)Delta_(j,s)-Delta_(j,s-1))`.  Thus `HWO` is
**equivalent**, after cancelling a positive integer, to

```text
4 ell |R_(j,s) Delta_(j,s) - Delta_(j,s-1)|
  <= (R_(j,s)-1)(j-1)2^ceil(n/2).                     (NSD)
```

This is the preferred direct theorem statement.  For the remaining orders,
`2^s>Q` and maximality of `Q` give `2^s>ell/(3c)`.  Hence
`d_s<3c` and the subgroup `2^s E_j` underlying `P_(j,s)` has only
`2^d_s < 8ell^3` elements.  The remaining obstacle is therefore a uniform
signed discrepancy among polynomially many, highly sparse ray classes; the
polynomial cardinality alone is not a bound, but it is a meaningful reduction
from an exponential family and should be the starting point for any direct
counting or geometric construction.

It is not, however, an averaging shortcut.  At the largest exact order at
conductor `j`, namely the least power of two `q_j>j`, one has
`q_j E_j={1}`.  Therefore

```text
P_(j,log2 q_j)=N_n^[j](1),
Delta_(j,log2 q_j)=2N_n^[j](1)-N_n^[j-1](1)=H_j(1),
```

where `N_n^[r](1)` denotes the degree-`n` Mangoldt population of the identity
class in `E_r`.

The top-order instance of `(NSD)` still contains the identity-ray increment
itself (paired only with the next nested power subgroup).  Thus the reduction
isolates the hard sparse system but does not make it a generic small-set
counting problem; any proof must use its signed nesting or an additional
arithmetic/geometric structure.

## What is established, and what must not be silently reused

- Wrapped characteristic-two inverse-additive energy is proved.  It supplies
  the required bilinear input but does not prove the signed order-family
  cancellation in `HWO`.
- The displayed four-population formula, exact character counts, low-order
  Weil payment, and all endpoint implications are replayed by independent
  native checks.  These are theorem reductions, not finite extrapolations.
- The stronger finite diagnostic
  `|T_(j,s)| <= j^2(j-1)2^ceil(n/2)` is false: at the level-23 even endpoint
  its required coefficient is 710, above its allowance 529.  This does **not**
  refute `HWO`.
- Bounding characters or Galois orbits separately cannot work: it discards the
  signed cancellation in `T_(j,s)` and reintroduces the known conductor loss.
- The fourth-moment/short-interval geometry of Hast--Matei is structurally
  relevant, but it is not an available proof.  Its estimates are for fixed
  degree in the `q -> infinity` regime; their constants may depend on degree,
  and for moments above two they assume `p>n`.  More importantly, even a
  characteristic-two extension of that theorem would not provide the uniform
  constant needed here.  See [Hast--Matei](https://arxiv.org/abs/1604.02067),
  especially Theorem A/B and Remark 1.5.
- A focused check of [Gorodetsky--Kovaleva
  (2024)](https://doi.org/10.1112/blms.13057) likewise does not close `HWO`.
  Their uniform high-conductor theorem treats the special primitive character
  `chi_(k,psi)(f)=psi(p_(-k)(f))`.  Over `F_2` this is an order-two additive
  character; `HWO` has already paid all low orders and asks for complete
  higher-Witt exact-order families.  Their symmetry and sieve argument is a
  useful model, but it does not control the four-term higher-order trace.

## Precise questions for a specialist

1. Can the four-term `T_(j,s)` be realized as the trace of one *signed*
   Artin--Schreier--Witt/Carlitz object whose rank or effective Betti cost is
   polynomial in `j`, uniformly for `F_2` and `n=2ell+O(1)`?  A bound giving a
   factor `4ell` over the characterwise Weil envelope is sufficient; square
   root cancellation in every individual character is not required.
2. Does power-subgroup orthogonality (`g in 2^s E_j`, equivalently the
   substitution `x -> x^(2^s)`) expose a known wild ramification filtration,
   local Fourier transform, or conductor-dropping operation that controls the
   **four-term difference** directly?  Any estimate applied to the four terms
   separately is too weak.
3. Is there a fixed-field, growing-conductor theorem for a family of primitive
   Witt-vector Dirichlet characters that retains the average over a complete
   exact-order layer?  Katz--Sawin style results in the checked literature are
   large-field equidistribution statements and do not answer this.
4. If none is known, which of these is the right new theorem to attempt:
   a uniform signed trace estimate for the complete order layer, a relative
   trace estimate after summing high orders, or a connected fourth-moment
   estimate?  The first is the smallest statement currently known to close the
   endpoint without relying on cross-order cancellation.

## Reproducible entry points

- Exact algebra and endpoint price:
  [ADR-0591](../09-decisions/adr-0591-reconstruct-exact-order-traces-by-power-subgroup-orthogonality.md)
  and [ADR-0592](../09-decisions/adr-0592-pay-low-exact-orders-by-weil-and-isolate-high-witt-orders.md).
- Paper-facing one-sided target:
  [lemire-complete-proof.tex](lemire-complete-proof.tex).
- Full current reduction and negative-route record:
  [lemire-half-degree-irreducibles.md](lemire-half-degree-irreducibles.md).

An affirmative answer needs a proof with constants uniform in `ell`, a check
that the object is genuinely characteristic-two and prime-power-modulus
applicable, and a substitution into the displayed `HWO` inequality.  A finite
table, a large-`q` limit theorem, or a pointwise character bound is not enough.
