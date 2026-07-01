# Finite Simplicial Homology V0

This pack extends the topology lane with the first finite algebraic-topology
bridge. It treats a small simplicial complex as finite set data plus exact
integer/rational linear algebra.

The pack covers:

- closure of a finite simplicial complex under non-empty faces;
- oriented boundary replay for a two-simplex;
- the finite chain-complex identity `boundary(boundary(simplex)) = 0`;
- Betti-number rank replay for a three-edge circle over `Q`;
- checked rejection of a false boundary sign;
- a QF_LIA/Diophantine certificate for the false boundary coefficient;
- checked rejection of a false boundary-of-boundary cancellation coefficient;
- a QF_LIA/Diophantine certificate for that false cancellation coefficient;
- a Lean-horizon row for general algebraic topology.

## Concepts

- `field_topology`
- `field_set_theory_and_foundations`
- `field_linear_algebra`
- `field_abstract_algebra`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_linear_algebra`

## Trust Story

The validator parses vertices, simplices, chains, and coefficients from
machine-readable JSON. It recomputes face closure, alternating boundaries,
boundary-of-boundary cancellation, boundary-matrix ranks, and the listed cycle
generator using exact arithmetic. The promoted bad boundary coefficient and
boundary-of-boundary cancellation rows are also emitted as solver-form integer
equality contradictions and checked with Diophantine evidence.

This is finite replay evidence plus small checked QF_LIA certificates for the
bad coefficients. It does not prove homology invariance, exact sequences,
homotopy equivalence, cohomology operations, or higher-dimensional algebraic
topology.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
```
