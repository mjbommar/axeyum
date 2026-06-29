# Checks

## `direct-proof-modus-ponens-witness`

Expected result: `sat`.

The witness assignment has `p = true` and `q = true`. The validator checks
that the premise `p`, the implication `p -> q`, and the conclusion `q` all
hold.

## `contrapositive-equivalence-no-counterexample`

Expected result: `unsat`.

The validator enumerates all assignments to `p` and `q` and confirms there is
no counterexample to:

```text
(p -> q) == (!q -> !p)
```

## `proof-by-cases-no-counterexample`

Expected result: `unsat`.

The validator enumerates all assignments to `p` and `r` and confirms that
`p -> r` and `!p -> r` cannot both hold while `r` is false.

## `contradiction-refutation-unsat`

Expected result: `unsat`.

The validator enumerates all assignments to `p` and `q` and confirms that
`p`, `p -> q`, and `!q` cannot all hold.

The pack also carries
[`cnf/contradiction-refutation.cnf`](cnf/contradiction-refutation.cnf), a
deterministic DIMACS encoding of the same premise set:

```text
p
not p or q
not q
```

The focused regression

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_contradiction_refutation_emits_checked_drat_and_lrat
```

parses that CNF, emits a DRAT proof with untrusted search, checks the DRAT proof
independently, elaborates it to LRAT, and checks the LRAT proof independently.

## `invalid-converse-counterexample`

Expected result: `sat`.

The validator checks the listed assignment `p = false`, `q = true`, where
`p -> q` is true but `q -> p` is false.

## `general-natural-deduction-lean-horizon`

Expected result: `not-run`.

This row records the future proof-assistant target: soundness and proof
reconstruction for a formal proof system, not just finite Boolean replay.
