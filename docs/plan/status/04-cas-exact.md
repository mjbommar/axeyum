# Lane: cas-exact — LIB-6 exact rational input and computation

<!-- plan-section: lane-status -->

**CAS exact inputs (`WIP`, cas-exact, 2026-10-10).** Rust Rational already carries
promoted coefficients, but the big zero-test fallback narrowed them with getters
that panic. Fix uses exact big numerator/denominator conversion. Three fresh
integration controls passed: equality/replay/tamper, big refutation, and the
360-period payment against an independent Python Fraction (2859/2849 bits).
Python transport remains bounded. Private-snapshot guard mutation is running. Next: audit other promoted-value
boundaries, implement exact expression/Python arithmetic and amortization,
negative powers, pi and bounded text parsing. No LIB-6 completion is claimed.
