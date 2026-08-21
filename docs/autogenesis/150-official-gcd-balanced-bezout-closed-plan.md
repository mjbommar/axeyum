# Closed official-gcd balanced-Bézout specialization plan

Date: 2026-08-21

The accepted generic theorem has exactly two remaining inputs. This increment
will rebuild the already accepted target-owned gcd support kernel, compose the
generic theorem into that kernel, and specialize it with exactly:

- `Nat.gcd_zero_left`, declaration identity
  `f81aee8a1d8528ddf8b7be6007efbee190f2208cdef3dcfda9fa03a1f200175d`;
- `Nat.gcd_succ`, declaration identity
  `e41996f98e01e15b88e11773bb42db825bf271888ece2d002c193627a8392727`.

The new mode must replay both the generic composition and dependency-bound
specialization. Two complete invocations must independently import all four
proof-isolated inputs and emit byte-identical summaries without rendering any
proof, type, or theorem value. The final theorem must have an empty footprint
and direct dependencies exactly equal to the generic theorem and the two gcd
leaves.

Success grants only the unconditional official-gcd balanced-Bézout theorem.
Coprime-factor cancellation, the Fibonacci target, evaluation, facts, and the
ledger remain outside this increment.

```sh
python3 scripts/check-autogenesis-official-gcd-balanced-bezout-closed-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_closed_plan
```
