# Model

The carrier is the four total functions from `{0,1}` to itself:

```text
id   : 0 -> 0, 1 -> 1
flip : 0 -> 1, 1 -> 0
zero : 0 -> 0, 1 -> 0
one  : 0 -> 1, 1 -> 1
```

The operation is function composition. The table entry at row `f`, column `g`
is `f after g`.

The checker validates the monoid table in two ways. First it checks identity
and associativity directly over the table. Then it recomputes each table entry
from the finite function maps.

The units are `id` and `flip`; they form the two-element group inside the
monoid. The idempotents are `id`, `zero`, and `one`.

## Bad Associativity Certificate

For the rejected three-element table, exact replay computes:

```text
b*b = a
a*b = a
b*a = b
```

Associativity on the failing triple would require:

```text
(b*b)*b = b*(b*b)
```

Together with `a != b`, the linked `QF_UF` artifact is unsatisfiable by pure
EUF congruence and transitivity. The resource regression checks that Axeyum
emits independently rechecked `UnsatAletheProof` evidence with no trusted
reduction step.

General semigroup/monoid theory, Green's relations, presentations, free
monoids, and category-theoretic constructions remain proof-assistant horizon
material.
