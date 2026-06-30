# Model

The pack uses a two-term chain complex of free abelian groups with ordered bases
`e` in degree 1 and `v` in degree 0.

```text
d1 = [2] : Z<e> -> Z<v>
d0 = []  : Z<v> -> 0
```

Because `d0` is the zero map, `d0*d1` is the empty zero matrix. The image of
`d1` is `2Z<v>`, so the quotient `C0 / im(d1)` is `Z/2`. The degree-one
homology is zero because `ker(d1)` is zero.

The Smith-normal-form replay is deliberately minimal: for the one-entry matrix
`[2]`, the diagonal invariant is `[2]`, rank is `1`, and the torsion factor in
`H0` is `2`.

The malformed row claims that `v` is already a boundary. In this fixed model
that would require an integer `k` with `2*k = 1`, which the QF_LIA route rejects
with checked Diophantine evidence.
