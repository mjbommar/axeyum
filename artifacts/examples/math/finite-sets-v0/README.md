# Finite Sets V0

This pack covers the first core curriculum slice for `sets`: finite universes,
membership as characteristic bits, subset checks, and union/intersection
identities. It is deliberately small and replay-oriented.

The examples are the set-theory shadow of Axeyum's Bool/BV route:

- replay a distributive finite-set identity over one explicit universe;
- replay subset transitivity over nested finite sets;
- reject a malformed fixed distributive claim by recomputing both sides;
- DIMACS CNF proof route for the malformed distributive-law rejection.

These checks do not claim to prove ZFC set theory or general infinite-set
theorems. They establish a checked finite model pattern that later packs for
relations, functions, cardinality, topology, measure, and probability can reuse.

## Concepts

- `curriculum_sets`
- `field_set_theory_and_foundations`

## Trust Story

The current validator checks that every listed subset is contained in its finite
universe, then recomputes the claimed set operations directly. The `sat` rows
are accepted only when the replayed fixed witness satisfies the claim. The
`unsat` row is a bounded fixed-claim rejection: the checker recomputes both
sides of the malformed identity and confirms that equality fails on the listed
sets.

The CNF artifact
[`cnf/distributive-law-counterexample.cnf`](cnf/distributive-law-counterexample.cnf)
isolates the element `c`, whose membership differs between the two sides of the
malformed equality. The focused CNF regression parses that artifact, emits a
DRAT proof with Axeyum's proof-producing SAT core, elaborates it to LRAT, and
checks both proof objects independently. Universal set identities still require
future Bool/BV lowering evidence or a theorem-prover route.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_sets_distributive_counterexample_emits_checked_drat_and_lrat
```
