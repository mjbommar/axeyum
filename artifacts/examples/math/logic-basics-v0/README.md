# Logic Basics V0

This pack covers the first propositional-logic slice for
`propositional-logic`: SAT witness replay, tautology checking by negating the
claim, contradiction checking, Boolean equivalence, and a tiny CNF refutation by
truth-table enumeration.

The examples are exact finite Boolean artifacts:

- replay a satisfying assignment for `p and q`;
- reject a counterexample to excluded middle `p or not p`;
- reject a satisfying assignment for `p and not p`;
- reject a De Morgan equivalence counterexample;
- reject a tiny unsatisfiable CNF `(p) and (not p or q) and (not q)`.

These checks use exhaustive truth-table enumeration, not an emitted SAT proof.
The `tiny-cnf-refutation` row now also has a deterministic DIMACS artifact and
an in-tree CNF regression that emits DRAT, elaborates to LRAT, and checks both
proof objects. The other rows remain finite replay examples until they add
distinct Boolean regression pressure.

## Concepts

- `curriculum_propositional_logic`
- `field_logic_and_proof`

## Trust Story

The validator evaluates the original Boolean formulas under all assignments for
the named variables. A SAT row is accepted only after replaying the witness; an
UNSAT row is accepted only after exhaustive enumeration finds no satisfying or
counterexample assignment. The promoted CNF row additionally exercises the
untrusted proof-emission path while accepting the result only after the small
DRAT/LRAT checkers recheck the refutation.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
```
