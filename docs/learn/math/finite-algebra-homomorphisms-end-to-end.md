# End To End: Finite Algebra Homomorphisms

This lesson follows one finite algebra-homomorphism resource from operation
tables and a carrier map to replayed result and proof/evidence status. It uses
the
[finite-algebra-homomorphisms-v0](../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)
pack.

Concept rows:

- `curriculum_groups`, `curriculum_rings`, and
  `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra` and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `z4-to-z2-group-homomorphism` | `sat` | replay-only |
| `kernel-image-replay` | `sat` | replay-only |
| `quotient-first-isomorphism-replay` | `sat` | replay-only |
| `z4-to-z2-ring-homomorphism` | `sat` | replay-only |
| `bad-group-homomorphism-rejected` | `unsat` | checked |
| `general-isomorphism-theorems-lean-horizon` | `not-run` | lean-horizon |

The replay rows are finite operation-table checks. The pack does not claim the
general group or ring isomorphism theorems, ideal quotient theory, module
homomorphism theorems, category-theoretic universal properties, or infinite
algebra.

## Encode

The domain group is `Z/4Z` under addition:

```text
0, 1, 2, 3
```

The codomain group is `Z/2Z` under addition:

```text
0, 1
```

The map is reduction modulo `2`:

```text
f(0) = 0
f(1) = 1
f(2) = 0
f(3) = 1
```

## Replay Group Homomorphism Preservation

The checker verifies every source pair:

```text
f(a + b) = f(a) + f(b)
```

For example:

```text
1 + 3 = 0 mod 4
f(1 + 3) = f(0) = 0
f(1) + f(3) = 1 + 1 = 0 mod 2
```

The two sides agree. The validator repeats this across the full `4 x 4`
addition table.

## Replay Kernel And Image

The kernel is the preimage of the codomain identity:

```text
ker(f) = {x | f(x) = 0} = {0, 2}
```

The image is the range of the finite map:

```text
image(f) = {0, 1}
```

Both are recomputed from the map table. They are not trusted because the pack
listed them.

## Replay Quotient And Induced Map

The quotient by the kernel has two cosets:

```text
K  = {0, 2}
1K = {1, 3}
```

The quotient table is:

```text
K  + K  = K
K  + 1K = 1K
1K + 1K = K
```

The induced map sends:

```text
K  -> 0
1K -> 1
```

The checker verifies the cosets, recomputes the quotient operation from
representatives, checks that every element of a coset has the same image, and
checks that the induced map is a bijective homomorphism onto the image.

For example:

```text
1K + 1K uses representatives 1 and 1
1 + 1 = 2, and 2 in K
```

So `1K + 1K = K`.

## Replay Ring Homomorphism Preservation

The same parity map is also checked as a unital ring homomorphism from `Z/4Z`
to `Z/2Z`. The checker verifies:

```text
f(0) = 0
f(1) = 1
f(a + b) = f(a) + f(b)
f(a * b) = f(a) * f(b)
```

One multiplication row is:

```text
3 * 3 = 1 mod 4
f(3 * 3) = f(1) = 1
f(3) * f(3) = 1 * 1 = 1 mod 2
```

The ring row ties the same finite function table to both addition and
multiplication preservation.

## Check The Refutation

The bad row proposes this map:

```text
g(0) = 0
g(1) = 1
g(2) = 1
g(3) = 1
```

The checker rejects it on the pair `1, 1`:

```text
1 + 1 = 2 mod 4
g(1 + 1) = g(2) = 1
g(1) + g(1) = 1 + 1 = 0 mod 2
```

Because `1 != 0`, the map is not a group homomorphism.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for structure-preserving maps:

```text
untrusted fast search -> candidate map, kernel, image, quotient, induced map
trusted small checking -> table preservation, kernel/image, quotient replay
```

General isomorphism theorems, normal-subgroup and ideal quotient theory,
module homomorphisms, categorical universal properties, and infinite algebra
require Lean/mathlib-scale proof support.
