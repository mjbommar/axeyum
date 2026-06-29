# Function Composition V0

This pack deepens the `relations-and-functions` curriculum node with finite
function operations: composition, image/preimage, inverse tables, associativity,
and checked rejection of a false inverse claim.

The examples are:

- composition of two total finite function tables;
- image and preimage replay for a finite subset;
- inverse table replay for a finite bijection;
- associativity of composition for three concrete finite functions;
- checked counterexample evidence for a non-injective function with no inverse;
- a QF_UF/Alethe composition-application consistency conflict;
- a Lean-horizon row for general function extensionality and categorical laws.

## Concepts

- `curriculum_relations_and_functions`
- `curriculum_sets`
- `curriculum_cardinality`
- `field_set_theory_and_foundations`
- `field_discrete_math`

## Trust Story

The validator checks every row by replaying explicit finite function graphs.
It accepts function rows only after totality and single-valuedness checks, then
recomputes composition, image, preimage, inverse, and associativity tables.

This is finite checked evidence plus one proof-object row. The SMT-LIB artifact
in `smt2/composition-application-conflict.smt2` certifies a concrete composition
application conflict with pure EUF Alethe evidence. It does not prove function
extensionality, category-theoretic associativity, or inverse laws over arbitrary
types. Those remain Lean-horizon targets until kernel-checked artifacts exist.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/function-composition-v0
```
