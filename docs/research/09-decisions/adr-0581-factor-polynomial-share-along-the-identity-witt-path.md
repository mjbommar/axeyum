# ADR-0581: Factor polynomial share along the identity Witt path

Status: accepted
Date: 2026-08-21
Index-summary: Reduce the polynomial identity-cylinder share to logarithmically many non-concentrating binary energy splits

## Context

ADR-0580 selects the sufficient localization theorem

```text
16 ell^2 F_j(1) <= F_j(global)                         (PL2)
```

for every retained Haar level `c_0<j<=ell`.  This already asks for only a
polynomial saving, but it presents the identity cylinder as one opaque subset
of the global parent group.

For a fixed retained level `j`, put `M_0=F_j(global)`.  For
`1<=i<=c_0`, let `M_i` be the same nonnegative sibling-difference square mass
restricted to parents projecting to the identity in `E_i`.  The sets are
nested, so

```text
M_0 >= M_1 >= ... >= M_c0 = F_j(1).                    (PATH)
```

This is a different conductor filtration from the earlier fourth-moment
filtration of the complete class discrepancy: here the nonnegative function
being restricted is one fixed Haar layer `H_j^2`.

## Decision

Expose every exact mass and parent/child comparison in the typed
`IdentityCylinderEnergyPathStep` report.  Register the following stronger
sufficient candidate:

```text
for each retained j, at least ceil(log2(16 ell^2)) indices i satisfy
2 M_i <= M_(i-1).                                      (HB)
```

All other steps satisfy `M_i<=M_(i-1)` for free.  Multiplication along the
path therefore gives

```text
F_j(1) = M_c0 <= 2^(-r) M_0 <= M_0/(16 ell^2),
```

which is `(PL2)`.  The alternative inequality `4 M_i<=3 M_(i-1)` needs the
least exact integer `r` satisfying `4^r>=16 ell^2 3^r`.

The native `identity_cylinder_path_split_implication` operation computes both
prices without floating point.  At `ell=200`, `(HB)` asks for only 20
half-balanced splits among the 190 available coarse levels; the
three-quarter version asks for 47.  Across `200<=ell<=1024`, both required
counts fit strictly inside the available path for both endpoint parities.
These are deterministic implications, not proofs that the split inequalities
hold.

One split is now proved exactly.  Translation `f(x) -> f(x+1)` is a
degree-preserving automorphism of `GF(2)[x]` and preserves `Lambda`.  Put
`t=2^v_2(n)`.  Lucas parity says

```text
binom(n,r)=0 mod 2 for 0<r<t,   binom(n,t)=1 mod 2.
```

On a polynomial whose first `t-1` leading coefficients vanish, translation
therefore preserves those coefficients and toggles coefficient `t`.  At every
later refinement level `j`, its action on coefficient `j` has leading term
`a_j` with coefficient one, so it permutes the two level-`j` children and
preserves the squared sibling difference.  Thus it bijects the two children
of the identity energy path at level `t` and proves

```text
2 M_t = M_(t-1)                                         (TR)
```

whenever `t<=c_0`.  The native
`identity_cylinder_translation_split_implication` prices this theorem and the
finite exact paths independently check the equality.  At both first endpoints
`n=401,402`, `(TR)` lowers the remaining half-balanced count from 20 to 19.
When `n` is a power of two, `t=n>c_0`, so this particular symmetry supplies no
path split and is not a universal completion of `(HB)`.

## Evidence

- `identity_cylinder_conditional_variance` reconstructs `M_i` directly from
  the exact integer sibling differences and fails closed if a child mass grows
  or the last path mass disagrees with `F_j(1)`.
- The bounded CLI emits each parent and child mass, both exact comparisons,
  and the observed sufficient-step counts.
- Exact small rows show that half-balanced steps occur throughout the path and
  are not confined to one coordinate.  This is finite diagnostic evidence
  only; the first theorem-bearing range begins at `ell=200`.
- On every exact row, the path entry at `2^v_2(n)` is required to be exactly
  half-balanced whenever it lies inside the coarse path, independently
  checking `(TR)` against the population transform.
- The fact ledger keeps `(HB)` conjectured with no proof evidence or
  Autogenesis registration.

## Consequences

- A proof no longer needs uniform sharing at every split.  It may discard all
  but `O(log ell)` favorable coarse coordinates, independently for each of the
  `O(log ell)` retained Haar levels.
- A local spectral-gap, involution, or two-child comparison can receive
  endpoint credit as soon as it supplies the required number of split bounds;
  it need not control a complete fourth moment.
- `(HB)` is stronger than `(PL2)` and remains open.  The manuscript continues
  to state only `(REL)` as its minimal missing lemma.
