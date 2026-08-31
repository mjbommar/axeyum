# Lane: quadratic-reciprocity

Status: **in progress** (opened 2026-08-31)

## Task

Size, and if reachable close, the law of quadratic reciprocity for distinct
odd primes `p, q`:

```text
(p|q) * (q|p) = (-1)^((p-1)/2 * (q-1)/2)
```

The engine is `Int.gaussLemmaSignCount` (ADR-1130). The classical route from
there is **Eisenstein's lattice-point count**, which needs a rectangle of
lattice points partitioned by a diagonal. This kernel has no `Finset`, no
`List` and no `Prod`, so the open question this lane must answer FIRST is
whether Eisenstein routes around that absence (a finite family is a function
plus a bound, and `sumRange`/`sumRange_swap` exist) or hits the same wall
ADR-1135 named for determinant multiplicativity.

## Landed changes

_(none yet -- this is the opening commit)_
