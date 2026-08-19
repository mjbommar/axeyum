# Fibonacci checked-theorem receipt result

Date: 2026-08-19

## Result

The sealed `Nat.fib_add_two` candidate now has semantic theorem receipt
`395f6e80e6addbc69cca8ad560b312dadc31d623fe05f6b1603b5fa523622329`.
Two fresh imports reconstructed the fixed v3 plan, independently admitted the
exact theorem, and reissued the identical receipt. No search ran.

The receipt binds the r080 stream, target definition, fact ID, candidate
observation, exact goal/proof/declaration, v3 operation, and original budget.
Both the axiom footprint and direct theorem dependency set are empty.

## Credit boundary

The enclosing sealed observation is
`28f313c405614fa9b9de47d76216e01669754c9f84e397ecc8845a551115182f`.
It issues one semantic theorem receipt but records zero evaluation credit and
zero ledger writes. The fact remains open.

The next turn must register an exact operation whose executor consumes and
replays this receipt, then pass the ordinary prepare/apply/recovery transaction.
Only the durable admission event may establish the fact and trigger a frontier
recomputation for its children.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_checked_theorem_receipt
python3 scripts/check-autogenesis-nat-fib-checked-theorem-receipt.py
```

