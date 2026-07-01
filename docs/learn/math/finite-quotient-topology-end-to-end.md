# End To End: Finite Quotient Topology

This lesson follows one finite quotient-topology resource from quotient-map
fibers to representative consistency, preimage-open replay, saturated-open
image replay, and checked rejection of malformed quotient rows. It uses the
[finite-quotient-topology-v0](../../../artifacts/examples/math/finite-quotient-topology-v0/)
pack.

Concept rows:

- `field_topology`, `field_set_theory_and_foundations`, and
  `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets` and `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_finite_quotient_topology_replay`,
  `bridge_finite_topology_operator_homeomorphism`, `bridge_quotient_map`, and
  `bridge_partition_relation_roundtrip` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `quotient-map-fiber-witness` | `sat` | replay-only |
| `quotient-topology-witness` | `sat` | replay-only |
| `saturated-open-image-witness` | `sat` | replay-only |
| `bad-fiber-representative-rejected` | `unsat` | checked QF_UF/Alethe |
| `bad-quotient-open-rejected` | `unsat` | checked QF_UF/Alethe |
| `general-quotient-topology-lean-horizon` | `not-run` | Lean horizon |

All rows are finite. The pack checks one explicit source topology, quotient
map, quotient fibers, quotient-open family, and saturated-open subset. It does
not prove quotient-space universal properties, quotient-map theorem schemas,
or preservation/invariance theorems for arbitrary spaces.

## Encode

The source finite topology is:

```text
X = {a,b,c}
open(X) = {}, {a,b}, {a,b,c}
```

The quotient map identifies `a` and `b`:

```text
q(a) = p
q(b) = p
q(c) = r
```

so the quotient fibers are:

```text
p -> {a,b}
r -> {c}
```

The induced same-fiber equivalence relation is:

```text
a ~ a, a ~ b
b ~ a, b ~ b
c ~ c
```

## Replay The Quotient Topology

The quotient topology is defined by preimages:

```text
V is open in {p,r} iff q^{-1}(V) is open in X
```

The finite checker enumerates every subset of `{p,r}`:

```text
{}      -> {}
{p}     -> {a,b}
{r}     -> {c}
{p,r}   -> {a,b,c}
```

Only `{}`, `{p}`, and `{p,r}` have open preimages in `X`. Therefore the
quotient-open family is exactly:

```text
{}, {p}, {p,r}
```

The saturated-open row checks the same idea from the source side. The subset
`{a,b}` is a union of complete fibers, so it is saturated. It is also open in
`X`, its image is `{p}`, and `q^{-1}({p}) = {a,b}`.

## Check The Refutations

The first promoted bad row claims that two source representatives in the same
fiber have distinct quotient images. Replay computes:

```text
q(a) = p
q(b) = p
```

The source SMT-LIB artifact isolates the fixed representative conflict:

```text
q(a) = p
q(b) = p
q(a) != q(b)
```

The accepted evidence is an `UnsatAletheProof` checked by `Evidence::check`
over the committed artifact
[`bad-fiber-representative-alethe-conflict.smt2`](../../../artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-fiber-representative-alethe-conflict.smt2).

The second promoted bad row claims `{r}` is quotient-open. Replay computes:

```text
q^{-1}({r}) = {c}
```

but `{c}` is not open in the source topology. The source SMT-LIB artifact
isolates the fixed open-status contradiction:

```text
preimage({r}) is not open
preimage({r}) is open
open_status != not_open_status
```

The solver search is untrusted. The accepted evidence is an
`UnsatAletheProof` checked by `Evidence::check` over the committed artifact
[`bad-quotient-open-alethe-conflict.smt2`](../../../artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-quotient-open-alethe-conflict.smt2).

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-quotient-topology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_fiber_representative_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_open_emits_checked_alethe
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate quotient map, representative/open claim, or proof
trusted small checking -> finite topology replay, quotient representative replay,
                          quotient preimage replay, saturation replay,
                          checked Alethe evidence
remaining horizon -> quotient topology universal properties and theorem schemas
```

Use this page after
[End To End: Finite Topology](finite-topology-end-to-end.md) and before
[End To End: Finite Specialization Order](finite-specialization-order-end-to-end.md)
when you want the finite topology-to-quotient bridge. For the broad theorem
boundary, read
[Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md).
