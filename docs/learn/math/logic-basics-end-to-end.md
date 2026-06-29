# End To End: Logic Basics

This lesson follows one propositional-logic resource from Boolean assignments
and truth tables to replayed result and proof/evidence status. It uses the
[logic-basics-v0](../../../artifacts/examples/math/logic-basics-v0/) pack.

Concept rows:

- `curriculum_propositional_logic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `and-formula-sat-witness` | `sat` | checked |
| `excluded-middle-no-counterexample` | `unsat` | checked |
| `contradiction-unsat` | `unsat` | checked |
| `demorgan-equivalence-no-counterexample` | `unsat` | checked |
| `tiny-cnf-refutation` | `unsat` | checked |

The checked rows are exhaustive Boolean truth-table rows. The pack does not yet
emit a SAT proof object; deterministic CNF emission plus checked DRAT/LRAT
evidence is the graduation route for stronger UNSAT evidence.

## Encode

The pack works over named Boolean variables:

```text
p = true or false
q = true or false
```

A SAT row gives one assignment and asks the validator to replay the original
formula. An UNSAT row gives a finite set of variables and asks the validator to
enumerate every assignment.

For two variables, the whole search space is:

```text
p=false, q=false
p=false, q=true
p=true,  q=false
p=true,  q=true
```

The trusted checker is small because it only evaluates the fixed Boolean
formula under each assignment.

## Replay A SAT Witness

The first row claims that:

```text
p and q
```

is satisfied by:

```text
p = true
q = true
```

The checker evaluates:

```text
true and true = true
```

so the row is accepted as `sat`.

## Check Excluded Middle By Refutation

The excluded-middle row asks whether there is a counterexample to:

```text
p or not p
```

The validator enumerates both assignments:

```text
p=false: false or true  = true
p=true:  true  or false = true
```

No assignment falsifies the formula, so the counterexample search is checked
`unsat`.

## Check A Contradiction

The contradiction row asks whether any assignment satisfies:

```text
p and not p
```

The validator enumerates:

```text
p=false: false and true  = false
p=true:  true  and false = false
```

No assignment works, so the formula is checked `unsat`.

## Check De Morgan Equivalence

The De Morgan row searches for an assignment separating:

```text
not (p and q)
```

from:

```text
(not p) or (not q)
```

The validator checks all four assignments for `p,q`. In each row the two
formulas have the same truth value, so the separating-counterexample search is
checked `unsat`.

## Check A Tiny CNF Refutation

The final row checks the CNF:

```text
(p) and (not p or q) and (not q)
```

The clauses force:

```text
p = true
not q = true, so q = false
not p or q = false or false = false
```

Truth-table enumeration confirms that all four assignments fail at least one
clause, so the CNF is checked `unsat`.

This is a finite exhaustive refutation. A future stronger artifact should emit
the CNF and check a DRAT/LRAT proof.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for propositional logic:

```text
untrusted fast search -> candidate assignment or Boolean formula
trusted small checking -> formula evaluation, truth-table enumeration, CNF replay
```

Larger Boolean UNSAT claims should graduate to emitted CNF plus checked SAT
proof evidence. General proof automation and proof assistant integration remain
separate proof routes.
