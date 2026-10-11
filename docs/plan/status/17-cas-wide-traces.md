# Lane: cas-wide-traces — promoted coefficients and closed rational steps

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 wide trace evidence (`WIP`, cas-wide-traces, 2026-10-11).** Child
of435de8c46. ADR-6500 allocates opt-in v2 arithmetic and exact canonical wide
coefficients, preserving v1's checked-width contract. Source audit confirms
Rational::checked_add/mul decline promoted results; wide_add/mul opt in.
MultiPoly's normalizer uses the checked route, so codec widening alone cannot
establish wide trace support. BigWitness normalizes up to a positive scale and
cannot directly serve as a canonical exact-value witness.

`just brief rational_power_trace` was UNRESOLVED with 2971-fact positive control;
its stale shape inventory prevents a mathematical absence claim.

Parent guarded full CAS run: 2143 passed, 1 timing failure, 11 ignored. The
isomorphism test's stated single-thread budget failed under parallel tests at
10.24s; exact one-thread control passed in0.95s. Parent serial runner58007 CAS phase passed2144, 0 failed, 11 ignored, 359.38s;
solver/workspace phases remain live/uncredited. Parent full lint96940 passed all925 targets/27 crates with0
diagnostics. Source stays fixed there while new work proceeds in this child.

Implemented opt-in `wide_polynomial::normalize_with_limits` with promoting
Rational operations, 16384-bit intermediate cap, width-weighted work and bounded
syntax/degree/terms. Constant powers through512 and exact constant division are
supported; zero and symbolic denominators decline explicitly. Initial compile
mismatches corrected; focused v2 runner63138 passed3 tests, 0 failed/ignored,
0.07s, `/var/tmp/axeyum-cas-wide-polynomial-tests-v2.log`. These are arithmetic
backend results, not completed wide-trace evidence. The initial v1 lib filter
ran0 and was not credited; corrected integration suite16750 passed8, 0 failed/
ignored, `/var/tmp/axeyum-cas-wide-v1-integration.log`.

Next: v2 codec/step replay and recorded nonzero conditions; fresh Python and independent Fraction
amortization; private guard controls and broad gates. No wide-trace completion
or kernel-admission claim yet; the full user-feedback goal remains active.
