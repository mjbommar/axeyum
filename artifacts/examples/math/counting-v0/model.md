# Model

The pack uses ordinary finite integer counts:

```text
P(n, k) = n! / (n-k)!
C(n, k) = n! / (k! * (n-k)!)
C(n, k) = C(n-1, k-1) + C(n-1, k)
```

The pigeonhole row fixes a set of pigeons and holes. A placement is a function
from pigeons to holes. It is injective when no two pigeons map to the same hole.

## Axeyum Route

The intended route is a mix of LIA/enumeration for integer identities and
Bool/CNF for fixed pigeonhole refutations. This pack currently checks the finite
objects directly in the resource validator.
