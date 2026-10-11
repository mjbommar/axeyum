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
10.24s; exact one-thread control passed in0.95s. Parent serial full runner58007
is live/uncredited. Parent full lint96940 passed all925 targets/27 crates with0
diagnostics. Source stays fixed there while new work proceeds in this child.

Next: implement bounded wide polynomial arithmetic, v2 codec/replay, closed
constant powers and nonzero division; fresh Python and independent Fraction
amortization; private guard controls and broad gates. No wide-trace completion
or kernel-admission claim yet; the full user-feedback goal remains active.
