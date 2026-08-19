# Preregistered contract-to-theorem bridge control

Date: 2026-08-19

Outcome: the frozen control later succeeded exactly once; see the
[result](40-int-gcd-contract-theorem-control-result.md). This page preserves the
pre-execution selection boundary.

## Selection

The next bounded producer target is frozen as `Int.gcd_def`:

```text
forall i j : Int,
  Int.gcd i j = Nat.gcd (Int.natAbs i) (Int.natAbs j)
```

This is deliberately a calibration-only target. It is exactly the contract
bound by the first real `Int.gcd` source receipt, so it isolates one question:
can theorem admission consume the trace-backed receipt without reconstructing a
theorem-valued source witness or whitelisting its 52-theorem closure?

At preregistration time the producer had not run. Its fixed budget was:

| Control | Frozen value |
|---|---:|
| Operation | `trace-contract-reflexivity-v1` |
| Binders | 2 |
| Constructed nodes | 5 |
| Invocations | 1 |
| Retries | 0 |
| Required source-contract receipts | 1 |
| Required source axioms | 0 |
| Evaluation credit | 0 |
| Ledger writes | 0 |

Acceptance requires exact source-receipt replay, independent kernel acceptance,
an empty theorem axiom footprint, and one semantic theorem receipt. Any failure
is retained as the result; there is no fallback grammar.

## Real evaluation horizon

The top-down ranking keeps `Int.gcd_fib` as the real compounding target:

```text
forall m n : Int,
  Int.gcd (Int.fib m) (Int.fib n) = Nat.fib (Int.gcd m n)
```

It is the only reviewed `Int.gcd` consumer whose statement-only dependency
catalog exposes a concrete chain:

```text
Int.fib_neg ─┐
             ├─> Int.gcd_fib
Nat.fib_gcd ─┘
```

Both premises are open in Axeyum. The calibration bridge therefore comes first
to separate infrastructure failure from mathematical-premise failure. Success
will not make either premise established and will not raise `Int.gcd_fib`.

## Leakage boundary

The policy binds committed reviewed-statement metadata, fact-ledger status, and
the exact source-contract receipt. Historical diagnostic outcomes are excluded
from the machine selection inputs. Held-out outcomes and Mathlib proof bodies
remain forbidden.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control_policy
python3 scripts/check-autogenesis-int-gcd-contract-theorem-control-policy.py
```
