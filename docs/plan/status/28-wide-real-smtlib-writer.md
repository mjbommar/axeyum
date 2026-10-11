# Lane: wide-real-smtlib-writer — promoted Real constants cannot panic

<!-- plan-section: lane-status -->

**LIB-6 X0 / P0 (`WIP`, wide-real-smtlib-writer, 2026-10-11).**
Child 3d5ff4029. Source audit found write_script uses narrowing Rational
numerator()/denominator() on public Real constants, which panic for promoted
values. Writer now uses exact big accessors, preserving canonical signs and
Real decimals/quotients. Four promoted cases pass in one regression. Initial
fixtures mistakenly used bounded arithmetic; corrected to wide_mul/wide_neg.
Private original-source snapshot reproduces the numerator panic (one failed
test, exit101); fixed source passes. All SMT-LIB tests385 passed, no failures/
ignores; warning-denied Clippy passed11.09s.
ADR7300: exact bounded (4096-digit) wide decimal intake; promoted unary negation,
quotient/floor/is_int folds; FP rounder explicitly declines promoted values.
Round-trip controls6 passed, including zero divisor preservation; SMT/FP broad
run passed486 tests (before added zero control),0 failed/ignored. Clippy SMT/FP
passed; solver Clippy passed38.49s. New front-door2 passed after finding/fixing
NRA sign-narrowing panic; existing NRA controls12 passed (2021 filtered).
Doc plan/ADR/link gates passed. Private snapshot69c3e0d7d controls completed:
syntax baseline6 and NRA baseline12 passed; removing decimal cap, FP
representation and NRA sign guards each caused exactly one intended failure.
All sources restored bytewise. Full solver serial gate74254 running on final
source; no pass credited yet. Next: full gates, datatype export.
No solver-wide completion or integration claim. Overall goal stays active.
