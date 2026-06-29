# Checks

## `php-2-2-sat`

Expected result: `sat`.

Witness:

```text
p0 -> h0
p1 -> h1
```

This control case should replay by evaluating the original finite assignment
constraints.

## `php-3-2-unsat`

Expected result: `unsat`.

This is the teaching example for refutation:

```text
assume an injective assignment from 3 pigeons to 2 holes
derive contradiction
```

Current proof status: `proof-gap`. The intended graduation route is deterministic
CNF emission plus a checked LRAT/DRAT certificate.
