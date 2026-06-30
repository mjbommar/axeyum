# End To End: Finite Universal Coefficient Shadow

This lesson follows one finite algebraic-topology resource from a two-term
integer chain complex to a degree-one universal-coefficient shadow and a checked
bad group-identification row. It uses
[finite-universal-coefficient-shadow-v0](../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/).

Concept rows:

- `bridge_finite_universal_coefficient_shadow`,
  `bridge_finite_torsion_homology_replay`,
  `bridge_finite_cohomology_replay`, and
  `bridge_finite_chain_homology_replay` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`,
  `field_linear_algebra`, and `field_abstract_algebra` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `integer-cochain-complex-replay` | `sat` | replay-only |
| `degree-one-uct-shadow` | `sat` | replay-only |
| `bad-uct-zero-rejected` | `unsat` | checked |
| `qf-uf-bad-uct-h1-zero` | `unsat` | checked |
| `general-uct-theorem-lean-horizon` | `not-run` | lean-horizon |

The checked slice is deliberately small: one integer chain complex, one dual
cochain complex, one degree-one Hom/Ext bookkeeping row, and one source-linked
QF_UF/Alethe equality conflict. The pack does not prove the universal
coefficient theorem, naturality, splitting choices, Ext/Tor functor laws, exact
sequences, or arbitrary chain-complex statements.

## Encode The Chain Complex

The model reuses the torsion pack's two-term complex:

```text
C1 = Z<e>
C0 = Z<v>
d1(e) = 2v
```

As a matrix with row basis `v` and column basis `e`:

```text
d1 = [2]
```

The validator checks the basis sizes and matrix shape before it trusts any
homology or cohomology labels.

## Dualize To A Cochain Complex

The dual cochain groups are:

```text
C^0 = Hom(C0, Z) = Z<v*>
C^1 = Hom(C1, Z) = Z<e*>
```

The coboundary is the transpose of the boundary matrix:

```text
delta0 = d1^T = [2]
delta1 = 0
```

The validator recomputes `delta0 = d1^T`, checks the listed cochain
composition, and verifies that `delta1 * delta0` is zero.

## Replay The Invariants

For the chain complex:

```text
H0 = Z/2
H1 = 0
```

For the dual cochain complex:

```text
H^0 = ker(delta0) = 0
H^1 = coker(delta0) = Z/2
```

The validator checks these as finitely generated abelian-group invariants:

```text
0     -> free_rank = 0, torsion_factors = []
Z/2   -> free_rank = 0, torsion_factors = [2]
```

This is exact finite invariant replay for a one-entry Smith diagonal, not a
general finitely generated abelian-group classifier.

## Check The Degree-One Shadow

The degree-one universal-coefficient shape for cohomology is:

```text
0 -> Ext(H0, Z) -> H^1 -> Hom(H1, Z) -> 0
```

For this fixed complex:

```text
Ext(H0, Z) = Ext(Z/2, Z) = Z/2
Hom(H1, Z) = Hom(0, Z) = 0
H^1 = Z/2
```

So the checked shadow is:

```text
0 -> Z/2 -> Z/2 -> 0 -> 0
```

The validator recomputes the `Hom` and `Ext` terms from the listed group
invariants and checks that the exact-sequence labels match this fixed row.

## Reject The Bad Group Claim

The negative row claims:

```text
H^1 = 0
```

Finite replay computes:

```text
H^1 = Z/2
```

The pack first rejects the claim by comparing group invariants: the replayed
group has torsion factor `[2]`, while the claimed zero group has no torsion
factor.

The source SMT-LIB artifact isolates the same mismatch as a pure EUF conflict:

```text
H1_cohomology = Z2
H1_cohomology = Zero
Z2 != Zero
```

Axeyum emits `UnsatAletheProof` evidence for that equality contradiction, and
`Evidence::check` independently rechecks it.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-universal-coefficient-shadow-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_universal_coefficient_bad_h1_zero_emits_checked_alethe
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate group identity or equality conflict
trusted small checking -> finite chain/cochain invariant replay plus checked Alethe proof
remaining horizon -> general UCT, exact sequences, naturality, Ext/Tor laws, and invariance
```

For the torsion quotient that feeds this shadow, read
[End To End: Finite Chain-Complex Torsion](finite-chain-complex-torsion-end-to-end.md).
For F2 cochains and cup-product operations, read
[End To End: Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md)
and
[End To End: Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md).
