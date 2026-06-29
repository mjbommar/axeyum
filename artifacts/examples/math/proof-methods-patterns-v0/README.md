# Proof Methods Patterns V0

This pack deepens the `proof-methods` curriculum node with finite Boolean
checks for standard proof patterns. It complements
`proof-methods-refutation-v0`, which focuses on pigeonhole refutation and CNF
enumeration.

The examples are:

- direct proof as modus ponens;
- contrapositive equivalence by exhaustive truth-table checking;
- proof by cases as a no-counterexample row;
- contradiction/refutation as an unsatisfiable premise set;
- DIMACS CNF proof route for the contradiction/refutation row;
- checked counterexample evidence for the invalid converse inference;
- a natural-deduction Lean-horizon row.

## Concepts

- `curriculum_proof_methods`
- `curriculum_propositional_logic`
- `field_logic_and_proof`

## Trust Story

The validator uses deterministic Boolean assignment replay and truth-table
enumeration. Satisfiable rows must replay the listed assignment. Unsatisfiable
rows are checked by enumerating every assignment over the listed finite
variable set.

The CNF artifact
[`cnf/contradiction-refutation.cnf`](cnf/contradiction-refutation.cnf) encodes
the premise set `p`, `p -> q`, and `not q`. The focused CNF regression parses
that artifact, emits a DRAT proof with Axeyum's proof-producing SAT core,
elaborates it to LRAT, and checks both proof objects independently.

This is finite checked evidence. It is not a proof of soundness for a general
natural-deduction calculus, sequent calculus, or proof reconstruction engine.
Those broader proof-system claims stay under Lean horizon until kernel-checked
artifacts exist.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_contradiction_refutation_emits_checked_drat_and_lrat
```
