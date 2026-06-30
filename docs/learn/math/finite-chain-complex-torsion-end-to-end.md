# End To End: Finite Chain-Complex Torsion

This lesson follows one finite integer chain-complex resource from boundary
matrix data to a torsion quotient and a checked Diophantine obstruction. It
uses
[finite-chain-complex-torsion-v0](../../../artifacts/examples/math/finite-chain-complex-torsion-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`,
  `field_linear_algebra`, and `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_boundary_operator_replay`,
  `bridge_finite_chain_homology_replay`,
  `bridge_finite_torsion_homology_replay`, and
  `bridge_gcd_divisibility_witness` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `integer-chain-complex-replay` | `sat` | replay-only |
| `smith-normal-form-replay` | `sat` | replay-only |
| `torsion-generator-replay` | `sat` | replay-only |
| `bad-torsion-boundary-rejected` | `unsat` | checked |
| `qf-lia-bad-torsion-generator` | `unsat` | checked |
| `general-universal-coefficient-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite integer replay or a source-linked
QF_LIA/Diophantine certificate. The pack does not prove universal coefficient
theorems, Ext/Tor laws, exact sequences, chain homotopy invariance, or
topological invariance.

## Encode The Chain Complex

The model has one generator in degree one and one generator in degree zero:

```text
C1 = Z<e>
C0 = Z<v>
d1(e) = 2v
d0 = 0
```

As a matrix with row basis `v` and column basis `e`, the boundary map is:

```text
d1 = [2]
```

The validator checks the basis sizes, boundary-matrix shape, and the listed
composition:

```text
d0 * d1 = 0
```

That establishes the fixed data is a chain complex.

## Replay The Torsion Calculation

For the one-entry matrix `[2]`, the Smith diagonal is `[2]`. The image of `d1`
inside `C0` is therefore:

```text
im(d1) = 2Z<v>
```

So the degree-zero homology quotient is:

```text
H0 = C0 / im(d1) = Z / 2Z
```

The validator recomputes the rational rank, checks the listed Smith diagonal,
and verifies the free-rank bookkeeping:

```text
free rank H0 = 1 - rank(d1) - rank(d0) = 1 - 1 - 0 = 0
torsion factors H0 = [2]
free rank H1 = 1 - rank(d1) = 0
```

This is a tiny Smith-normal-form replay row, not a general Smith-normal-form
algorithm.

## Check The Generator

The class `[v]` has order two because:

```text
d1(1*e) = 2v
```

So `2[v] = 0` in the quotient. But `[v]` itself is not zero, because making
`v` a boundary would require:

```text
2*k = 1
```

for some integer `k`. The validator checks this divisibility obstruction
directly: `1` is not divisible by `2`.

## Check The Diophantine Certificate

The solver-form row isolates the same bad generator claim as QF_LIA:

```smt2
(declare-fun k () Int)
(assert (= (* 2 k) 1))
```

Axeyum emits an `UnsatDiophantine` certificate for the impossible equation and
checks it independently. That is the trusted negative artifact: search may find
the contradiction, but the accepted result is the replayed integer
non-divisibility proof object.

## Name The Lean Horizon

The finite pack checks:

```text
one finite free abelian chain complex
d0*d1 = 0
one Smith diagonal [2]
one torsion factor Z/2
one bad boundary-membership refutation
one QF_LIA/Diophantine certificate for 2*k = 1
```

The following remain proof-assistant targets:

```text
general Smith normal form
classification of finitely generated abelian groups
universal coefficient theorem
Ext and Tor functor laws
exact sequences
chain homotopy invariance
topological invariance of homology
```

Those stay Lean-horizon until there are no-sorry artifacts or replay
certificates that can be reconstructed in the theorem-prover layer.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chain-complex-torsion-v0
cargo test -p axeyum-solver --test math_resource_lia_routes finite_chain_complex_torsion_bad_generator_emits_checked_diophantine_evidence
```

Expected output for the pack validator:

```text
validated 1 foundational example pack(s)
```

## Related Lessons

Start with
[End To End: Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md)
for boundary matrices and Betti-rank replay. Continue to
[End To End: Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md)
and
[End To End: Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md)
for F2 cochains and cohomology operations.
