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
Bool/CNF for fixed pigeonhole refutations. The finite counting identities are
checked directly in the resource validator. The pigeonhole row also has a
source-level DIMACS artifact under `cnf/` and a Boolean DRAT/LRAT route
regression that checks the certificate path for the same fixed finite claim.
