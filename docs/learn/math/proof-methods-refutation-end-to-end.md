# End To End: Proof By Refutation

This lesson follows one proof-by-refutation resource from a finite pigeonhole
encoding to replayed result and proof/evidence status. It uses the
[proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)
pack.

Concept rows:

- `curriculum_proof_methods`, `curriculum_propositional_logic`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `php-2-2-sat` | `sat` | checked |
| `php-3-2-unsat` | `unsat` | checked |

The checked rows are finite Boolean pigeonhole rows. `PHP(3,2)` is currently
checked by deterministic CNF truth-table enumeration. LRAT/DRAT remains the
stronger graduation route for proof-object evidence.

## Encode

For `PHP(n,m)`, introduce one Boolean variable per pigeon/hole pair:

```text
x_p_h = pigeon p is assigned to hole h
```

The finite constraints are:

```text
every pigeon chooses at least one hole
no pigeon chooses two different holes
no two pigeons share one hole
```

The refutation pattern is:

```text
claim is valid  <=>  negation of claim is UNSAT
```

For pigeonhole, the impossible negated claim is an injective placement of more
pigeons than holes.

## Replay The SAT Control

The `PHP(2,2)` witness is:

```text
p0 -> h0
p1 -> h1
```

as Boolean assignments:

```text
x_p0_h0 = true
x_p0_h1 = false
x_p1_h0 = false
x_p1_h1 = true
```

The checker verifies every pigeon chooses exactly one hole and no hole receives
two pigeons. This small SAT control proves the validator is checking the
intended constraints rather than rejecting all pigeonhole encodings.

## Check The Refutation

The main row is `PHP(3,2)`. It asks for an injective assignment of:

```text
p0, p1, p2
```

into:

```text
h0, h1
```

The deterministic CNF uses variables:

```text
x_p0_h0, x_p0_h1
x_p1_h0, x_p1_h1
x_p2_h0, x_p2_h1
```

For each pigeon, the CNF includes:

```text
at least one hole: x_p_h0 or x_p_h1
at most one hole:  not x_p_h0 or not x_p_h1
```

For each hole, it includes clauses forbidding two pigeons in the same hole:

```text
not x_p0_h0 or not x_p1_h0
not x_p0_h0 or not x_p2_h0
not x_p1_h0 or not x_p2_h0
```

and the matching clauses for `h1`.

The validator enumerates all `2^6 = 64` Boolean assignments and finds no
satisfying row, so the CNF is checked `unsat`.

## Keep Proof Objects Separate

Truth-table enumeration is checked finite evidence. It is not the same artifact
as a SAT proof certificate. The graduation path is:

```text
deterministic CNF -> SAT solver UNSAT -> emitted DRAT/LRAT -> checked proof
```

This distinction matters for Axeyum's identity: fast search can be untrusted,
but the returned evidence should be small and independently checkable.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for proof by refutation:

```text
untrusted fast search -> candidate placement or UNSAT result
trusted small checking -> SAT witness replay, deterministic CNF enumeration, future LRAT/DRAT check
```

Larger refutation examples need emitted CNF and checked proof certificates
before they should be called proof-object covered.
