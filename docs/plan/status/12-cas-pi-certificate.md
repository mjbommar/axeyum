# Lane: cas-pi-certificate — source-bound exact enclosure bytes

<!-- plan-section: lane-status -->

**Pi enclosure transport (`WIP`, cas-pi-certificate, 2026-10-11).** Isolated
child of 087fc31b5; parent broad runner64759 retains immutable source. ADR-6200
specifies version1 source-bound single-Pi Machin evidence, exact endpoints,
remainder/order, precision up to256 and resource caps. Rust/Python transport,
producer and counted replay implemented. Four Rust controls pass, including
precision256. Fresh native rebuild and nine Python suites pass283/zero skips,
including a separate-process certificate replay. Stub generation and runtime
name/arity/type gates pass. Source-binding mutation passes (four baseline;
three pass/one failure when the guard is removed). Format, focused CAS Clippy,
link and plan-authority checks pass. Broad runner43938 is live on56fe5378d:
full CAS suite terminal pass: 2,140 passed, 0 failed, 11 ignored, 373.02s
(`/var/tmp/axeyum-pi-certificate-full-gates-_dy3bzlq/cas_lib.log`).
Workspace libraries remain live; no workspace pass credited. Replay never
invokes production; parsing alone grants no acceptance.
Tamper tests require wrong-source, understated remainder and invalid endpoint/
precision declines; conservative relaxations retain the verifier semantics.
Next: workspace gates, general enclosure transport and checked Pi
value inequalities; retain byte/source checking through reconstruction. General enclosure transport,
checked Pi inequalities and kernel reconstruction remain separate open work.
