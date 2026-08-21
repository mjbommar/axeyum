# ADR-0585: Kill the top Witt shifted trace before pricing lower cohomology

Status: accepted
Date: 2026-08-21
Index-summary: Apply joint Witt monodromy to eliminate the top-cohomology term in every nontrivial high-character shift while retaining the fixed-binary lower-cohomology trace as open

## Context

ADR-0583 writes each aggregate identity-path split as an exact-conductor layer
of

```text
C_(j,n)(eta)
 = sum_(cond psi=j) S_n(psi) conjugate(S_n(psi eta^(-1))),   (C)
```

where `cond(eta)<j` and `S_n` is the degree-`n` Mangoldt character sum.
ADR-0584 expands the same integer into a signed two-Mobius polynomial sum.
The closest published theorem must therefore control the joint family
`L(psi),L(psi eta^(-1))`, not merely the marginal distribution of `L(psi)`.

Sawin's universal Witt-character construction does exactly this at the level
of geometric monodromy.  Take his two fixed geometrically nonisomorphic rank
one sheaves

```text
F_1 = 1,        F_2 = L_(eta^(-1)),
```

and twist both by the variable primitive character `psi` of `W_(j,q)`.  The
two resulting L-functions are those of `psi` and `psi eta^(-1)`.  His main
geometric theorem and product-monodromy argument apply for `j>=4` in every
characteristic; the paper's asymptotic is in `q`, but the geometric monodromy
statement itself has no `p>j` or odd-characteristic hypothesis.

## Decision

Use the product monodromy only for what it proves uniformly: elimination of
the top cohomology invariant.

For a primitive even character of `W_(j,q)`, the normalized degree-`n`
Mangoldt sum is the power-sum character

```text
p_n(U)=trace(U^n)
```

on the rank `N=j-1` Frobenius space.  The symmetric-function identity

```text
p_n = sum_(r=0)^min(n-1,N-1) (-1)^r s_(n-r,1^r)          (H)
```

decomposes it into hook representations.  A polynomial irreducible
representation of `GL_N` restricts trivially to `SL_N` only when its partition
is a rectangle `(a^N)`.  No hook in `(H)` is such a rectangle unless `n=N`.
At a Lemire endpoint `n in {2ell+1,2ell+2}` and `j<=ell`, one has
`N=j-1<n`.  Hence `p_n` has no `SL_N`-invariant summand.

Sawin's joint geometric monodromy contains the product of the two special
linear groups.  Therefore the external character

```text
p_n(U_1) conjugate(p_n(U_2))
```

has no invariant vector.  In the Lefschetz trace formula over the
`j`-dimensional primitive Witt-parameter space, its top compactly supported
cohomology vanishes:

```text
H_c^(2j)(Prim_j,
  Adams_n(G_j) tensor Adams_n(t_eta^* G_j)^vee) = 0.      (TOP0)
```

Here `Adams_n` denotes the virtual sheaf whose trace is `p_n`; `(TOP0)` is an
identity in the Grothendieck group, equivalently the vanishing of the top term
hook by hook.  It applies to every nontrivial `eta` of conductor below `j`.

Do **not** substitute Sawin's equidistribution conclusion into the endpoint
ledger.  After `(TOP0)`, Deligne weights place the remaining terms in degrees
at most `2j-1`, giving a formal `q^(-1/2)` weight drop multiplied by their
total Betti complexity.  At `q=2` the factor is only `2^(-1/2)`, and the paper
provides no bound uniform in the growing conductor or in the growing Adams
power `n`.  Sawin explicitly says that such uniformity is likely possible but
is not pursued, because his theorem fixes the sheaves and conductor and lets
`q` tend to infinity.

Thus the live geometric lemma is now the lower-cohomology statement

```text
(WITT-LOW)
the complete signed Frobenius trace in degrees <=2j-1,
summed over the requested exact-conductor eta layer and over j>c,
satisfies ADR-0584's exact contraction price.                       (WL)
```

An absolute total-Betti estimate is sufficient only if it is inserted into
the native price and closes it at `q=2`; top-weight vanishing or an
`O_(j,n)(q^(-1/2))` statement alone receives no credit.  Cancellation in the
alternating lower-cohomology trace may prove `(WL)` even when a total-Betti
bound is too large.

## Evidence

- Sawin identifies the character parameter space with affine `j`-space,
  constructs the universal Artin--Schreier--Witt sheaf, and proves that the
  product geometric monodromy contains the relevant special-linear factors
  for conductor at least four.
- His proof of equidistribution kills top cohomology exactly when the chosen
  representation has no geometric invariants, then bounds all lower degrees
  by weights.  `(H)` verifies the no-invariant hypothesis at every Lemire
  endpoint and every `j<=ell`.
- The rank formula gives `N=j-1` for the constant sheaf and for a fixed lower
  conductor rank-one twist once the variable conductor is `j`.
- The exact CAS report from ADR-0584 remains the quantitative arbiter: neither
  `(TOP0)` nor a qualitative weight drop changes its contraction booleans.

## Consequences

- The required shifted family is not an invented local system; it is the
  rank-one specialization of a published joint Witt-monodromy construction.
- Characteristic two is not the obstruction at the product-monodromy step.
  The obstruction is fixed-`q` control of lower cohomology while `j` and the
  Adams power grow together.
- Hast--Matei `m=2` and Sawin's Witt family are two presentations of the same
  remaining geometry: coefficient-pair covariance versus character-parameter
  Fourier transform.  The latter proves the top invariant is absent.
- Lemire's conjecture, `(REL)`, every unforced aggregate contraction, and
  `(WITT-LOW)` remain unproved.

## References

- Will Sawin, [*The equidistribution of L-functions of twists by Witt vector
  Dirichlet characters over function fields*](https://arxiv.org/abs/1805.04330),
  especially the main geometric theorem, the joint product-monodromy
  corollary, and the final Lefschetz argument.
- Nicholas Katz, [*Witt vectors and a question of Keating and
  Rudnick*](https://web.math.princeton.edu/~nmk/wittchar25.pdf), for the
  universal big-Witt character sheaf and primitive monodromy family.
- Hast and Matei, [*Higher moments of arithmetic functions in short
  intervals: a geometric perspective*](https://arxiv.org/abs/1604.02067), for
  the two-polynomial coefficient-space presentation.
