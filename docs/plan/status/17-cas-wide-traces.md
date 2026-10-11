# Lane: cas-wide-traces — promoted coefficients and closed rational steps

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 wide trace evidence (`WIP`, cas-wide-traces, 2026-10-11).** Child
of435de8c46. ADR-6500 specifies v2 arithmetic/codec while retaining v1 width and
domain limits. Promoted normalization bounds intermediate coefficients at16384
bits, width-weighted work, shape/expansion/degree, and constant powers at512.
Three arithmetic tests passed. V2 traces retain source/endpoints, local witnesses,
continuity/premises/context and per-step certificates; v1 remains narrow.

Added v2 constant-divisor wire/head and explicit nonzero side-condition binding.
Original-input domain validation also rejects an empty trace for division by0.
Symbolic divisors require the separate external-context guarded API. Current
Rust suites: 8 v1 + 7 v2 passed, 0 failed/ignored, v2 1.49s;
`/var/tmp/axeyum-cas-wide-division-tests.log`. V2 includes full exact 360-period
amortization with two checked division steps, missing conditions and empty
undefined-quotient controls. An earlier zero-test lib filter was uncredited;
all v1 credit comes from the integration suite.

Python `normalize_trace(..., wide=True)` opts in; default remains v1. Getters
and source-bound replay transport wide values without narrowing. Fresh native
68539 passed; sealed package
`/data0/axeyum/artifacts/python/cas-wide-trace-zyb2jcxy/package`, SHA256
`8d15fa2aa3664369c9031fbe191aeeb46032fe11720ea15072d74e45dde83f55`;
imported native path verified. 34 Python trace tests passed, 0 skipped, 9.07s,
`/var/tmp/axeyum-cas-wide-python-tests.log`. Independent Fraction comparisons
cover positive/negative/zero rates and zero principal; separate-process payment
replay does not call the producer. Updated amortization example verifies bytes.
Stub generation launched, `/var/tmp/axeyum-cas-wide-stubs.log`, not credited.

Parent guarded full CAS serial gate: 2144 passed/0 failed/11 ignored/359.38s;
full lint: 925 targets/27 crates/0 diagnostics. Its earlier parallel timing
failure is retained in parent evidence. Parent solver/workspace runner58007
remains uncredited. These are parent results, not this child's broad gates.

Next: stub validation, private v2 guard mutations and own broad gates; wide
symbolic guarded quotients, cost measurements, kernel reconstruction and branch
integration remain open. The entire feedback goal stays active.
