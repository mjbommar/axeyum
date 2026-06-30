# End To End: Finite Simplicial Homology

This lesson follows one finite algebraic-topology resource from simplicial
complex data to boundary and Betti-rank replay. It uses
[finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`,
  `field_linear_algebra`, and `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_chain_homology_replay` in the Foundational Concept Atlas.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `simplicial-complex-closure` | `sat` | replay-only |
| `oriented-boundary-replay` | `sat` | replay-only |
| `boundary-squared-zero` | `sat` | replay-only |
| `betti-rank-replay` | `sat` | replay-only |
| `bad-boundary-rejected` | `unsat` | checked |
| `qf-lia-bad-boundary-coefficient` | `unsat` | checked |
| `general-homology-lean-horizon` | `not-run` | lean-horizon |

Every checked row is finite set and exact integer/rational linear-algebra
replay. The pack does not prove homology invariance, exact sequences, homotopy
equivalence, cohomology, or general algebraic topology.

The shared `bridge_finite_chain_homology_replay` row is the atlas vocabulary
for this finite chain-complex slice. It lets consumers find the exact replay
and checked Diophantine coefficient route without treating the finite row as a
general algebraic-topology theorem.

## Replay Simplicial Closure

The filled triangle witness lists vertices:

```text
a, b, c
```

and simplices:

```text
[a], [b], [c]
[a,b], [a,c], [b,c]
[a,b,c]
```

The checker verifies that every non-empty face of every listed simplex is also
listed. It also checks the dimension counts:

```text
0-simplices = 3
1-simplices = 3
2-simplices = 1
```

This is finite set closure, not a general theorem about all complexes.

## Replay An Oriented Boundary

The oriented boundary row fixes the two-simplex:

```text
[a,b,c]
```

The validator recomputes the alternating face sum:

```text
d([a,b,c]) = [b,c] - [a,c] + [a,b]
```

The signs matter: deleting vertex `a` gives `[b,c]` with sign `+`, deleting
`b` gives `[a,c]` with sign `-`, and deleting `c` gives `[a,b]` with sign `+`.

## Replay Boundary Squared Is Zero

The chain-complex row applies the boundary twice:

```text
d([a,b,c]) = [b,c] - [a,c] + [a,b]
```

Then the checker expands each edge boundary:

```text
d([b,c]) = [c] - [b]
d([a,c]) = [c] - [a]
d([a,b]) = [b] - [a]
```

with the middle term carrying coefficient `-1`. The vertex coefficients cancel:

```text
([c]-[b]) - ([c]-[a]) + ([b]-[a]) = 0
```

That proves `boundary^2 = 0` for this finite simplex by exact replay.

## Replay A Betti-Rank Calculation

The circle witness removes the filled two-simplex and keeps the three edges:

```text
[a,b], [a,c], [b,c]
```

It records chain dimensions:

```text
dim C0 = 3
dim C1 = 3
dim C2 = 0
```

and boundary ranks over `Q`:

```text
rank d1 = 2
rank d2 = 0
```

The validator builds exact rational boundary matrices, computes ranks by
Gaussian elimination, and checks:

```text
b0 = dim ker d0 - rank d1 = 3 - 2 = 1
b1 = dim ker d1 - rank d2 = (3 - 2) - 0 = 1
```

It also checks the listed cycle generator:

```text
[a,b] - [a,c] + [b,c]
```

has zero boundary.

## Reject A Bad Boundary Sign

The negative row claims:

```text
d([a,b,c]) = [b,c] + [a,c] + [a,b]
```

The checker recomputes the actual boundary and finds the first mismatch:

```text
simplex = [a,c]
claimed coefficient = 1
actual coefficient = -1
```

So the false boundary-sign row is rejected by exact integer coefficient replay.

## Check The Boundary Coefficient Certificate

The solver-form row isolates the same sign error as integer equalities. The
actual coefficient of `[a,c]` is:

```text
coeff_ac = -1
```

The bad claim requires:

```text
coeff_ac = 1
```

Axeyum emits an `UnsatDiophantine` certificate for those inconsistent
equalities and checks it independently. That keeps the educational boundary
replay tied to the project identity: search can propose a boundary row, but
the accepted negative claim has a small checked integer certificate.

## Name The Lean Horizon

The finite pack checks:

```text
finite face closure
oriented boundary replay
boundary squared zero for a fixed simplex
boundary-matrix rank replay over Q
Betti-number replay for a fixed circle
bad boundary-sign refutation
QF_LIA boundary-coefficient contradiction
```

The following remain proof-assistant targets:

```text
homology invariance
long exact sequences
homotopy equivalence
cohomology operations
higher-dimensional algebraic topology
```

Those stay Lean-horizon until no-sorry artifacts or finite rank certificates
can be reconstructed into the theorem-prover layer.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite homology resource pattern:

```text
untrusted fast search -> complex, boundary, rank, cycle, or bad-boundary row
trusted small checking -> finite face enumeration, exact linear algebra, and Diophantine certificates
remaining horizon -> general algebraic-topology theorems
```

The graduation target is to encode fixed finite simplicial complexes as
deterministic finite-set and integer-linear-algebra obligations, replay
boundary and Betti rows through Axeyum model evaluation, and add emitted
certificates for false-boundary and rank rows once finite matrix proof routes
are promoted.
