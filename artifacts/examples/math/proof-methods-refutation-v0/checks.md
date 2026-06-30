# Checks

## `php-2-2-sat`

Expected result: `sat`.

Witness:

```text
p0 -> h0
p1 -> h1
```

The validator replays the finite assignment constraints: every pigeon chooses
exactly one hole, and no hole receives two pigeons.

## `php-3-2-unsat`

Expected result: `unsat`.

This is the teaching example for refutation:

```text
assume an injective assignment from 3 pigeons to 2 holes
derive contradiction
```

Current proof status: `checked` by deterministic CNF truth-table enumeration.
The pack records the PHP(3,2) CNF clauses directly and the validator enumerates
all 64 assignments.

The source CNF artifact is [`cnf/php-3-2.cnf`](cnf/php-3-2.cnf). The Boolean
route regression parses that DIMACS file, emits a DRAT proof, elaborates it to
LRAT, and checks both certificates:

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_emits_checked_drat_and_lrat
```
