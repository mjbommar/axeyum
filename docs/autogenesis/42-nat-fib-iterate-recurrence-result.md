# First bounded Fibonacci recurrence result

Date: 2026-08-19

## Result

The preregistered `Nat.fib_add_two` operation ran once and did not establish
the theorem. The zero-target preflight first proved that the generic iterator
successor helper itself is well typed. During the sole target execution, direct
normalization was rejected as expected, then the recurrence plan was rejected:

```text
TypeMismatch { expected: ExprId(171), got: ExprId(0) }
```

There was no retry. `Nat.fib_add_two` remains open, and this result receives no
semantic theorem receipt, evaluation credit, or ledger write. The sealed
negative observation has semantic identity
`a5b3ec307e060c5da6a7255ef39fe8f9d568ddf1d15f9988e72ecbabe9f7eaa3`.

## What changed in our model

The first missing capability is narrower than “prove Fibonacci recurrence.”
The imported `Nat.fib` iterator shape is usable, and a locally constructed
induction proof establishes the reusable successor equation. The failure occurs
when two projected equalities are composed into the target equation through
the hand-built `Eq.rec` terms.

That is useful negative evidence: expanding induction search, importing
Mathlib proof bodies, or changing the strategic target would all skip the
measured boundary.

## Next bounded turn

Work bottom-up on a target-independent equality-elimination microbench:

1. render the exact imported `Eq.rec` telescope and universe order;
2. test fresh `congrArg` and equality-transitivity constructors on synthetic
   reflexive and non-reflexive equalities;
3. require stage-by-stage inferred types and readable mismatch diagnostics;
4. freeze those constructors and their hashes before preregistering a second
   `Nat.fib_add_two` execution.

Top-down, the strategic sequence is unchanged:

```text
Nat.fib_add_two
  -> Nat.fib_coprime_fib_succ
  -> Nat.gcd_fib_add_self
  -> Nat.fib_gcd
  -> Nat.fib_dvd and Int.gcd_fib
```

## Reproduction

The target operation must not be rerun. Verify the retained result instead:

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_nat_fib_iterate_recurrence_result
python3 scripts/check-autogenesis-nat-fib-iterate-recurrence-result.py
```

