# Model

The chain complex is:

```text
C1 = Z<e>
C0 = Z<v>
d1(e) = 2v
```

Its homology invariants are:

```text
H0 = Z/2
H1 = 0
```

The dual cochain complex uses the transpose map:

```text
C^0 = Hom(C0, Z) = Z<v*>
C^1 = Hom(C1, Z) = Z<e*>
delta0 = d1^T = [2]
```

So:

```text
H^0 = ker(delta0) = 0
H^1 = coker(delta0) = Z/2
```

For this fixed degree-one case, the universal-coefficient ingredients are:

```text
Hom(H1, Z) = Hom(0, Z) = 0
Ext(H0, Z) = Ext(Z/2, Z) = Z/2
```

The pack checks those finite invariant calculations. It does not prove the
universal coefficient theorem for arbitrary complexes.
