# Exact `Int.gcd_fib` construction plan

`Int.fib_neg` closed the last explicit dependency of `Int.gcd_fib`, and the
authoritative frontier now selects the latter. This plan freezes the first
bounded construction before any new source is compiled or proof-bearing stream
is read. It does not consult or transport Mathlib's proof of the target.

The useful intermediate statement is

```lean
∀ (m : ℤ), (Int.fib m).natAbs = Nat.fib m.natAbs
```

Call its target-owned form
`Axeyum.Autogenesis.intFibNatAbsV1`. Mathematically it says that the sign
extension used by integer Fibonacci disappears when `natAbs` is taken. The
positive constructor is definitional. The negative constructor must be reduced
through the already admitted exact `Int.fib_neg` theorem and independently
checked, target-owned `natAbs` transport; an assumption-bearing simplifier is a
decline rather than a usable result.

Once that bridge is clean, the final composition is short:

```text
gcd (fib m) (fib n)
  = gcd (natAbs (fib m)) (natAbs (fib n))       by the exact Int.gcd equation
  = gcd (Nat.fib (natAbs m)) (Nat.fib (natAbs n))
  = Nat.fib (gcd (natAbs m) (natAbs n))         by admitted Nat.fib_gcd
  = Nat.fib (Int.gcd m n)                       by the exact Int.gcd equation
```

The machine-readable authority is
[`mathlib-int-gcd-fib-construction-plan-v1.json`](../../artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v1.json).
Its checker verifies that both prerequisite facts are currently proved, their
sealed capsules still have their exact bytes, the target remains open, and the
first execution has no target-submission or ledger-write authority.

```sh
python3 scripts/check-autogenesis-int-gcd-fib-construction-plan.py
```

On a clean bridge result, the next increment will preregister the exact
four-part target composition before constructing `Int.gcd_fib`. On a nonempty
footprint, the measured dependency carrier becomes the next bottom-up leaf.
