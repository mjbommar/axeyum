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
Next: wide decimal reader round trips, datatype source export, broad gates.
No solver-wide completion or integration claim. Overall goal stays active.
