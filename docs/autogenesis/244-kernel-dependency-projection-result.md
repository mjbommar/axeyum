# 244 — Kernel-observed dependency projection

Date: 2026-08-24

## Result

F2 of the [knowledge-overlay plan](243-knowledge-overlay-and-fill-plan.md) now
has a generated kernel projection at
[`kernel-dependency-projection-v1.json`](../../artifacts/autogenesis/kernel-dependency-projection-v1.json).
It is a sidecar: it changes no theorem source, fact, operation, or admission
rule.

The current constructed-prelude run contains 1,122 distinct declarations:

| Kind | Count |
|---|---:|
| Theorem | 855 |
| Definition | 171 |
| Inductive | 20 |
| Constructor | 26 |
| Recursor | 20 |
| Axiom | 30 |
| Total direct theorem dependency edges | 4,035 |

Each declaration retains all constructed preludes in which it is visible, its
declaration kind, and the size of its kernel-derived axiom footprint. Each
edge is a direct theorem-to-theorem reference read from an accepted proof term.
Definitions, inductives, constructors, recursors, axioms, opaque constants,
and quotient declarations are represented as nodes but do not receive
invented proof-dependency edges.

## What this makes explicit

- A direct theorem dependency is not a transitive closure.
- A kernel-derived edge is not a human fact-planning `depends_on` edge.
- A theorem, definition, inductive, constructor, and recursor are different
  node kinds; scheduler queries cannot accidentally treat a recursor as a
  proved proposition.
- A declaration's presence is separate from whether a theorem's footprint
  reaches an assumed declaration. The projection preserves both declaration
  kind and footprint size rather than publishing one blended trust badge.
- The same canonical declaration may be visible in multiple nested preludes;
  it remains one node with multiple visibility records, not duplicate facts.

## Controls

```sh
python3 scripts/validate-autogenesis-kernel-dependency-projection.py
python3 -m unittest scripts.tests.test_validate_autogenesis_kernel_projection
python3 scripts/gen-autogenesis-kernel-dependency-projection.py --check
just autogenesis-kernel-projection
```

The negative controls reject a missing generated edge, a non-theorem endpoint,
and a projection whose edge list no longer exactly agrees with the declaration
records. The generator itself reruns the kernel and fails on a stale artifact;
the validator refuses an environment with fewer than 700 declarations.

## Next

F3 should normalize retained producer-decline episodes into typed obstructions.
The scheduler can then join a ready fact to its direct kernel support and to
the measured capability gap, without promoting either planning annotations or
heuristics into admission authority.
