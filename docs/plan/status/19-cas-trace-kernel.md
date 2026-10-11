# Lane: cas-trace-kernel — stepwise trust-anchor reconstruction

<!-- plan-section: lane-status -->

**LIB-5 T3 (`WIP`, cas-trace-kernel, 2026-10-11).** Child ofb0e327536.
ADR6700 specifies syntax-preserving step translation and kernel proof composition
through existing Complex ring laws. Existing cas_bridge_tests proves whole
univariate integer identities, not serialized step traces. Next: implement
trace-driven before/after translation, compose proofs, admit generated identity,
measure axiom footprint, reject altered statement/assumptions, release validation.
Implemented syntax translator for bounded integer ring expressions and a generated
multistep trace test: byte replay, before/after kernel terms, transitivity,
admission, measured empty footprint, altered-endpoint rejection. Release job44600
compiling, uncredited: `/var/tmp/axeyum-cas-trace-kernel-test.log`.
Parent guarded full lint passed927 targets/27 crates/0 diagnostics; not a child
lint result. All broader feedback requirements remain active.
