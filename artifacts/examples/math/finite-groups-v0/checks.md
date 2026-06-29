# Checks

## `z4-addition-group-table`

Expected result: `sat`.

The witness lists the Cayley table for addition modulo `4`. The validator checks
closure, two-sided identity `0`, inverses, and associativity.

## `z4-inverse-table`

Expected result: `sat`.

The witness lists the inverse of every element in `Z/4Z` under addition:

```text
0 -> 0
1 -> 3
2 -> 2
3 -> 1
```

The validator checks each entry against the Cayley table.

## `subtraction-mod3-non-group`

Expected result: `unsat`.

The checked query is the fixed false claim that subtraction modulo `3` forms a
group operation. The validator confirms the table fails the group axioms.

## `qf-uf-group-operation-congruence-alethe`

Expected result: `unsat`.

The SMT-LIB artifact treats the group operation as a binary uninterpreted
function. It asserts equal operands pairwise, but demands unequal products. The
solver regression requires a pure EUF `Evidence::UnsatAletheProof` and rechecks
it independently.
