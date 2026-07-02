# Chain Complex Torsion Theorem Boundary

This page is the finite/general boundary for
[finite-chain-complex-torsion-v0](../../../artifacts/examples/math/finite-chain-complex-torsion-v0/).
It explains what Axeyum currently checks, what is only replayed, and what must
remain a Lean/theorem horizon.

Companion learner pages:

- [End To End: Finite Chain-Complex Torsion](finite-chain-complex-torsion-end-to-end.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md)
- [Matrix Computation Index](matrix-computation-index.md)
- [Topology Theorem Boundary](topology-theorem-boundary.md)
- [Linear Algebra Structure Theorem Boundary](linear-algebra-structure-theorem-boundary.md)

## Current Finite Resource

The pack fixes one two-term free abelian chain complex:

```text
C1 = Z<e>
C0 = Z<v>
d1(e) = 2v
d0 = 0
```

With row basis `v` and column basis `e`, the boundary matrix is `[2]`. The
validator checks the matrix shape and the chain-complex law:

```text
d0 * d1 = 0
```

For this single matrix, the Smith diagonal is `[2]`, so:

```text
im(d1) = 2Z<v>
H0 = Z/2Z
H1 = 0
```

The class `[v]` has order two because `2v` is a boundary. The class `[v]` is
not itself zero because making `v` a boundary would require an integer solution
to:

```text
2*k = 1
```

## Evidence Rows

| Row | Result | Evidence Status | What It Means |
|---|---|---|---|
| `integer-chain-complex-replay` | `sat` | replay-only | The listed matrices form the fixed chain complex. |
| `smith-normal-form-replay` | `sat` | replay-only | The one-entry Smith diagonal and torsion bookkeeping match the fixed data. |
| `torsion-generator-replay` | `sat` | replay-only | `2[v] = 0` and `[v] != 0` in the fixed quotient. |
| `bad-torsion-boundary-rejected` | `unsat` | checked | Divisibility replay rejects the claim that `v` is a boundary. |
| `qf-lia-bad-torsion-generator` | `unsat` | checked | QF_LIA/Diophantine evidence rejects `exists k. 2*k = 1`. |
| `general-universal-coefficient-lean-horizon` | `not-run` | lean-horizon | General UCT, Ext/Tor, invariance, and exact-sequence claims are not proved here. |

## Trusted Boundary

The trusted finite part is exact integer arithmetic over the listed matrix:

- basis names and dimensions
- boundary-matrix shape
- the zero composition `d0*d1`
- the one-entry Smith diagonal `[2]`
- quotient bookkeeping for `Z/2Z`
- the divisibility obstruction for `2*k = 1`
- the checked `UnsatDiophantine` artifact for the SMT-LIB contradiction

The replay-only rows are useful finite witnesses. They are not proof objects
for arbitrary chain complexes. The checked rows are narrow negative artifacts
for the malformed torsion-generator claim.

## Not Proved Yet

This resource does not prove:

- a general Smith-normal-form algorithm
- classification of finitely generated abelian groups
- quotient-module normal-form correctness for arbitrary integer matrices
- universal coefficient theorem
- Ext and Tor functor laws
- exact-sequence theorem schemas
- naturality or splitting statements
- chain-homotopy invariance
- topological invariance of homology
- homotopy-equivalence, spectral-sequence, or cohomology-operation claims

Those are theorem-prover targets. Finite matrix replay can provide examples and
regression pressure, but it must not be displayed as general algebraic topology
coverage.

## Query It

From the repository root, show the theorem boundary and the finite shadow:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-chain-complex-torsion-v0 \
  --require-any
```

Show the Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-chain-complex-torsion-v0 \
  --proof-status lean-horizon \
  --require-any
```

Show the checked Diophantine rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-chain-complex-torsion-v0 \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-chain-complex-torsion-v0 \
  --route Diophantine \
  --proof-status checked \
  --text torsion \
  --require-any
```

Show concept-scoped torsion rows without hard-coding the pack id:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_torsion_homology_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

## Graduation Criteria

Promote this boundary only after the future proof route has:

- precise theorem statements for chain complexes over `Z`, finitely generated
  abelian groups, Smith normal form, Ext/Tor, exact sequences, chain homotopy,
  and topological invariance
- explicit hypotheses for bases, boundary maps, quotient groups, finite
  generation, functorial maps, naturality, and splitting choices
- no-`sorry` Lean artifacts or another kernel-checkable proof route
- an axiom audit for every imported theorem
- reconstruction links from finite quotient certificates into the theorem layer
- labels that keep replay-only, checked Diophantine, and Lean-horizon rows
  distinct in downstream displays

Until then, the pack is a strong finite example and a useful solver/proof
regression seed, not a general theorem result.
