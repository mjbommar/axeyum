# Corrected Fibonacci recurrence v2 result

Date: 2026-08-19

## Result

The sole v2 `Nat.fib_add_two` execution was rejected:

```text
TypeMismatch { expected: ExprId(4557), got: ExprId(6266) }
```

There was no retry. The sealed observation has semantic identity
`f69f0c6815e8d57a57e590756e62a8b08cdbf489673db648a159f20d14c0e9f1`.
The fact remains open, with zero theorem receipts, evaluation credit, and
ledger writes.

## What v2 established

All pre-execution controls passed exactly. In particular, the generic
`Eq.rec.{0,1}` transitivity and congruence declarations were independently
accepted with no axioms or theorem dependencies. The v1 mismatch
`expected Prop; got Sort 1` did not recur.

The new mismatch therefore lies later: the target-specific projected
equalities do not yet compose at the type the kernel expects. This is narrower
than the v1 boundary and rules out both the iterator helper and generic
equality-eliminator universe order as the remaining first cause.

## Next bounded turn

Do not preregister v3 yet. First add a zero-submission stage control that:

1. infers the specialized iterator-helper applications;
2. infers the first `Prod.fst` congruence and compares its rendered type to the
   intended left-to-middle equality;
3. does the same for the `Prod.snd` congruence;
4. infers their transitivity application; and
5. compares only then against the rendered r080 goal.

Every stage must report canonical expected/inferred identities and readable
types. This will distinguish a wrong projection, wrong helper specialization,
wrong equality orientation, or insufficient definitional reduction without
another target submission.

The strategic horizon is unchanged: `Nat.fib_add_two` remains the prerequisite
for `Nat.fib_coprime_fib_succ`, then `Nat.gcd_fib_add_self`, `Nat.fib_gcd`, and
its two downstream unlocks.

## Reproduction

The target operation must not be rerun. Verify both retained negative results:

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_iterate_recurrence_result
python3 scripts/check-autogenesis-nat-fib-iterate-recurrence-result.py
```

