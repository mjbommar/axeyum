# Checks

## `z4-ring-table`

Expected result: `sat`.

The witness lists addition and multiplication modulo `4`. The validator checks
the finite ring axioms over the full table.

## `z4-zero-divisor-witness`

Expected result: `sat`.

The witness checks that `2` and `2` are nonzero in `Z/4Z` while:

```text
2 * 2 = 0 mod 4
```

This shows the finite ring is not an integral domain.

## `non-distributive-table-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim that the listed two-operation table
satisfies distributivity. The validator enumerates all triples and finds a
counterexample.

## `non-distributive-table-qf-bv-drat`

Expected result: `unsat`.

For the failing triple `(a=1,b=0,c=0)`, the finite table computes:

```text
a*(b+c)       = 1
(a*b)+(a*c)   = 0
```

The QF_BV artifact records the resulting fixed-width contradiction. The solver
regression parses that artifact, proves it `unsat`, exports the bit-blasted
CNF with a DRAT refutation, and rechecks the certificate independently.

## `bad-multiplicative-identity-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim that the listed two-operation table
has `1` as a multiplicative identity. The table has XOR-like addition and zero
multiplication, so the additive group and multiplication associativity replay,
but the identity law fails:

```text
1 * 1 = 0
```

## `bad-multiplicative-identity-qf-bv-drat`

Expected result: `unsat`.

For the claimed identity `one=1` and element `1`, the finite table computes:

```text
one * element = 0
required      = 1
```

The QF_BV artifact records the resulting fixed-width contradiction. The solver
regression parses that artifact, proves it `unsat`, exports the bit-blasted
CNF with a DRAT refutation, and rechecks the certificate independently.
