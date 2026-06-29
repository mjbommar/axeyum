# Algebra And Number Theory

Concept rows:

- `field_abstract_algebra` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_modular_arithmetic`, `curriculum_divisibility_and_euclid`, and
  `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [finite-groups-v0](../../../artifacts/examples/math/finite-groups-v0/)
- [finite-monoids-v0](../../../artifacts/examples/math/finite-monoids-v0/)
- [finite-permutation-groups-v0](../../../artifacts/examples/math/finite-permutation-groups-v0/)
- [finite-group-actions-v0](../../../artifacts/examples/math/finite-group-actions-v0/)
- [finite-rings-v0](../../../artifacts/examples/math/finite-rings-v0/)
- [finite-algebra-homomorphisms-v0](../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)
- [finite-ideals-v0](../../../artifacts/examples/math/finite-ideals-v0/)
- [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/)
- [finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/)
- [finite-modules-v0](../../../artifacts/examples/math/finite-modules-v0/)
- [finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/)
- [gcd-bezout-v0](../../../artifacts/examples/math/gcd-bezout-v0/)
- [modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [number-theory-v0](../../../artifacts/examples/math/number-theory-v0/)
- [finite-fields-v0](../../../artifacts/examples/math/finite-fields-v0/)
- [polynomial-identities-v0](../../../artifacts/examples/math/polynomial-identities-v0/)
- [polynomial-factorization-rational-v0](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)
- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)

## What Axeyum Checks

The current algebra path is finite and exact. It checks finite group Cayley
tables, finite ring operation tables, gcd/Bezout witnesses, CRT witnesses,
modular inverses, composite non-units with no inverse, and a Fermat-style finite
unit enumeration. The finite-rings pack adds distributivity checks and a `Z/4Z`
zero-divisor witness. The finite-monoids pack checks a finite transformation
monoid under function composition, recomputes its units and idempotents, and
rejects a non-associative table. The finite-permutation-groups pack checks
`S3` as bijective function tables under composition, recomputes cycle lengths
and signs, checks the sign homomorphism, replays the natural action, and
rejects a non-bijection. The finite-group-actions pack checks a finite group
acting on a finite set, recomputes orbits and stabilizers, replays the
orbit-stabilizer cardinality equation, and checks Burnside fixed-point
averaging for the same action. The finite-algebra-homomorphisms pack adds exact
structure-preserving map checks: group homomorphism replay, kernel/image
recomputation, quotient and induced-map replay, ring homomorphism replay, and
bad-homomorphism rejection. The finite-ideals pack checks finite ideals,
principal ideal generation, ring-homomorphism kernels, and quotient-ring
tables over modular rings. The finite-vector-spaces pack checks finite fields
acting on finite additive groups, subspaces, spans, linear maps, kernels,
images, and rank-nullity. The finite-dual-spaces pack checks covectors as
finite field-valued function tables, pointwise dual operations, dual-basis
pairing, annihilator recomputation, transpose maps, and bad-covector
refutations. The finite-modules pack checks finite rings acting on finite
additive groups, generated submodules, module homomorphisms, quotient module
tables, kernels, images, and bad-submodule refutations. The
finite-tensor-products pack checks finite tensor-product basis/dimension
replay, bilinear maps, factorization through a tensor map, Kronecker products,
and bad-bilinear-map refutations. The gcd/Bezout
pack adds exact divisibility and fixed linear Diophantine checks. The
number-theory pack adds bounded CRT
compatibility, quadratic residues, sum-of-two-squares, and Diophantine replay.
The finite-fields pack adds a complete inverse table for `F_7`, exhaustive
distributivity checking in `F_5`, and a `Z/6Z` non-field contrast.
The polynomial pack adds exact coefficient replay, factor-theorem witnesses, and
fixed false-root rejection. The rational polynomial-factorization pack adds
factor-list product replay, polynomial long division, Euclidean GCD replay,
square-free decomposition replay, and a checked irreducible-quadratic rejection.
The complex pack adds algebraic real-pair arithmetic and a fixed polynomial-root
witness.

These examples teach algebra as data that can be replayed: a candidate inverse
either multiplies to `1` modulo `n`, or it does not.

## Encode / Check Walkthrough

Start with a finite group table small enough to check by hand:

```text
Z/4Z under addition
0 + 1 = 1
1 + 3 = 0
2 + 2 = 0
```

The `finite-groups-v0` pack checks closure, identity, inverses, and
associativity for the full Cayley table.

For a finite monoid example, use all total functions on `{0,1}` under
composition:

```text
id, flip, zero, one
flip after flip = id
zero after flip = zero
one after zero = one
units = {id, flip}
idempotents = {id, zero, one}
```

The `finite-monoids-v0` pack checks identity and associativity, recomputes the
composition table from the four finite functions, recomputes units and
idempotents, and rejects a malformed table with a concrete associativity
failure.

For a finite permutation-group example, use `S3` as bijections on `{1,2,3}`:

```text
r   = (1 2 3)
r2  = (1 3 2)
s12 = (1 2)
s13 = (1 3)
s23 = (2 3)
sign(r) = even
sign(s12) = odd
stabilizer(1) = {e, s23}
```

The `finite-permutation-groups-v0` pack checks the `S3` group table, recomputes
each table entry from function composition, recomputes cycle lengths and
parity signs, verifies sign multiplication, and checks the natural action's
orbit-stabilizer count.

For a finite group-action example, let `C2 = {e,s}` act on two-bit strings by
swapping the middle strings:

```text
s.00 = 00
s.01 = 10
s.10 = 01
s.11 = 11
orbit(01) = {01, 10}
stabilizer(01) = {e}
fixed(e) = 4
fixed(s) = 2
orbits = (4 + 2) / 2 = 3
```

The `finite-group-actions-v0` pack checks the identity and compatibility
action laws, recomputes the sample orbit and stabilizer, verifies
`|orbit(x)| * |stabilizer(x)| = |G|`, recomputes all action orbits, and
checks Burnside's fixed-point average.

For a finite ring example, use `Z/4Z`:

```text
2 * 2 = 0 mod 4
```

The `finite-rings-v0` pack checks the addition and multiplication tables, then
replays `2` and `2` as nonzero zero divisors. Next move from structures to
maps:

For a finite homomorphism, reduce `Z/4Z` modulo `2`:

```text
f(0) = 0
f(1) = 1
f(2) = 0
f(3) = 1
ker(f) = {0, 2}
```

The `finite-algebra-homomorphisms-v0` pack checks `f(a + b) = f(a) + f(b)` for
every pair, recomputes kernel and image, verifies the quotient by the kernel,
and checks the same map as a unital ring homomorphism.

For a finite ideal and quotient-ring example, use even residues in `Z/6Z`:

```text
(2) = {0, 2, 4}
E = {0, 2, 4}
O = {1, 3, 5}
O * O = O
```

The `finite-ideals-v0` pack checks ideal closure under addition and ring
multiplication, recomputes the principal ideal generated by `2`, checks the
modulo-`2` ring homomorphism kernel/image, and verifies the quotient-ring
addition and multiplication tables.

For a finite vector-space example, use `F2^2`:

```text
vectors = 00, 10, 01, 11
span(10) = {00, 10}
projection(01) = 00
projection(11) = 10
```

The `finite-vector-spaces-v0` pack checks the scalar action laws, recomputes
the span of `10`, checks the projection is linear, recomputes kernel and image,
and verifies rank-nullity as `2 = 1 + 1`.

For a finite dual-space example, represent covectors on `F2^2` as tables:

```text
x(10) = 1
x(01) = 0
y(10) = 0
y(01) = 1
annihilator({00,10}) = {zero,y}
```

The `finite-dual-spaces-v0` pack checks that each covector is linear, dual
addition and scalar multiplication are pointwise, `x,y` pair with the primal
basis as the identity matrix, the annihilator is exactly the covectors that
vanish on the listed subspace, and the transpose map satisfies
`(T* phi)(v) = phi(Tv)`.

For a finite module example, use `Z/4Z` acting on itself:

```text
2 * 1 = 2
2 * 2 = 0
submodule generated by 2 = {0, 2}
quotient cosets = {0, 2}, {1, 3}
```

The `finite-modules-v0` pack checks the module action laws, recomputes the
submodule generated by `2`, checks multiplication by `2` as a module
homomorphism, recomputes kernel and image, and verifies the quotient-module
addition and scalar-action tables.

For a finite tensor-product example, use `F2^2 tensor F2`:

```text
(10 tensor 1) maps to 10
(01 tensor 1) maps to 01
beta(11, 1) = 11
```

The `finite-tensor-products-v0` pack checks the listed basis tensors span the
finite tensor space, verifies bilinearity of `beta(v,a) = a*v`, checks a
finite universal-factorization shadow through a linear projection, recomputes
a fixed Kronecker product over `F2`, and rejects a malformed bilinear table.

The number-theory bridge starts with a Bezout witness:

```text
252*4 + 198*(-5) = 18
```

The `gcd-bezout-v0` pack recomputes `gcd(252,198) = 18`, checks the listed
common divisors, and rejects `6*x + 10*y = 15` because `gcd(6,10)` does not
divide `15`. Then move to a modular inverse witness:

```text
3 * 5 = 15 == 1 mod 7
```

The `modular-arithmetic-v0` pack encodes that as `a = 3`, `modulus = 7`, and
`inverse = 5`. The validator recomputes the product modulo `7`; no theorem
about all moduli is needed to trust this witness.

The bounded destination pack adds fixed number-theory shapes:

```text
4^2 == 5 mod 11
65 = 1^2 + 8^2
14*(-1) + 21*1 = 7
```

The `number-theory-v0` pack also checks that no residue squares to `3 mod 7`
and that no sum of two integer squares equals `7`.

For a field-flavored example, the `finite-fields-v0` pack lists every nonzero
inverse in `F_7`:

```text
2 * 4 = 8 == 1 mod 7
3 * 5 = 15 == 1 mod 7
6 * 6 = 36 == 1 mod 7
```

It also checks that no residue `b` satisfies `2*b == 1 mod 6`, showing the
fixed composite modulus is not a field.

For a polynomial-flavored algebra example, the polynomial pack encodes
`x^2 - 5x + 6` as `[6, -5, 1]`, checks `p(2) = 0`, and verifies:

```text
x^2 - 5x + 6 = (x - 2)(x - 3)
```

The factorization pack then moves from one root witness to exact rational
polynomial arithmetic:

```text
x^4 - 1 = (x - 1)(x + 1)(x^2 + 1)
(x^4 - 1) / (x - 1) = x^3 + x^2 + x + 1
gcd(x^3 - x, x^2 - 1) = x^2 - 1
```

It also checks a square-free decomposition for
`(x - 1)^2*(x + 2) = x^3 - 3x + 2` by recomputing `gcd(p,p') = x - 1`, and
rejects a rational linear factorization claim for `x^2 + 1` using the exact
negative discriminant.

The complex pack then encodes `i` as the real pair `[0, 1]`. The validator
squares the pair and checks:

```text
i^2 + 1 = [-1, 0] + [1, 0] = [0, 0]
```

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rings-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ideals-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-fields-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-factorization-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

For fuller traces from transformation-monoid, permutation, and action-table
data through replay, read [End To End: Finite Monoids](finite-monoids-end-to-end.md),
[End To End: Finite Permutation Groups](finite-permutation-groups-end-to-end.md),
and [End To End: Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md).

## Horizon

General group, permutation-group, monoid, group-action, ring, field, module, isomorphism-theorem, quotient, and
algebraic-number-theory theorems need Lean-backed concept rows. Near-term
resource gaps are stronger BV/CNF or EUF/Alethe evidence for finite group,
finite monoid, finite permutation-group, finite group-action, finite ring, finite homomorphism,
finite ideal, finite vector-space, finite dual-space, finite-field, finite-module,
gcd/Diophantine, bounded number-theory, and fixed-degree polynomial universal
rows.
